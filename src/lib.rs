pub mod ivl;
mod ivl_ext;

use std::vec;
use std::collections::{HashMap, HashSet};
use uuid::Uuid;
use std::iter::zip;
use ivl::{IVLCmd, IVLCmdKind, WeakestPrecondition};
use slang::ast::{Block, Cmd, CmdKind, Expr, ExprKind, Ident, MethodRef, Name, Op, Range, Type};
use slang_ui::prelude::*;
use slang_ui::prelude::slang::ast::{Cases, PrefixOp, Case};
use slang_ui::prelude::slang::Span;

pub struct App;

#[derive(Debug, Clone)]
struct MethodContext {
    name: Name,
    variant_assertion : Expr,
    post_conditions: Vec<Expr>,
    global_variables_old_values: HashMap<Ident, (Ident, Type)>
}

#[derive(Debug, Clone)]
struct LoopContext {
    variant_assertion : Expr,
    invariants: Vec<Expr>,
}

impl LoopContext {
    pub fn empty() -> Self {
        LoopContext {
            variant_assertion: Expr::bool(true),
            invariants: Vec::new()
        }
    }
}

fn get_fresh_var_name(ident: &Ident) -> Ident {
    let id = Uuid::new_v4();
    return Ident(format!("{}_{}", ident.0, id.to_string()).to_string());
}

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &mut slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;


        // Iterate methods
        for m in file.methods() {
            if let None = m.body {
                continue;
            }
            //println!("Checking method {}", m.name);
            // Get method's preconditions;
            let pres = m.requires();
            // Merge them into a single condition
            let pre = pres
                .cloned()
                .reduce(|a, b| a & b)
                .unwrap_or(Expr::bool(true));
            // Convert the expression into an SMT expression
            let spre = pre.smt()?;
            // Assert precondition
            // Why do we assert the preconditions?
            // Reason: 
            // We are interested in the validity of each of the following predicates in the set
            // because we are "assuming the preconditions":
            // {pre_condition -> wp_predicate : forall wp_predicate in wp_list(body)[post_conditions]}
            // However, we check for satisfiability of !(precondition -> wp_predicate)
            // which is equivalent to !(!precondition or wp_predicate) == precondition and !wp_predicate
            // Therefore we assert the precondition and later on assert the negation of each of the wp_predicate's
            solver.assert(spre.as_bool()?)?;

            let post_conditions: Vec<Expr> = m.ensures().map(|e| e.clone()).collect();

            let mut ivl = IVLCmd::nop();

            // We assign the values of global variables to some fresh variables
            // to replace with old later on
            let mut global_variables_old_values: HashMap<Ident, (Ident, Type)> = HashMap::new();
            let mut specified_global_variables = HashSet::new();
            for (name, ty) in m.modifies() {
                let global_var_old_name = get_fresh_var_name(&name.ident.clone());
                global_variables_old_values.insert(name.ident.clone(), (global_var_old_name.clone(), ty.clone()));
                specified_global_variables.insert(name.ident.0.clone());
                ivl = ivl.seq(&IVLCmd::assign(
                    &Name { span: name.span, ident: global_var_old_name },
                    &Expr::ident(&name.ident.clone(), ty)
                ));
            }

            let variant_assertion = match &m.variant {
                Some(variant_expr) => {
                    let variant_name = get_fresh_var_name(&Ident(String::from("variant")));
                    let variant_assignment = IVLCmd::assign(&Name { span: variant_expr.span, ident: variant_name.clone() }, &variant_expr);
                    let mut variant_base = Expr::new_typed(ExprKind::Infix(Box::new(Expr::ident(&variant_name.clone(), &Type::Int)), Op::Ge, Box::new(Expr::num(0))), Type::Bool);
                    ivl = ivl.seq(&variant_assignment).seq(&IVLCmd::assert(&variant_base, "Variant might not always be >= 0"));
                    variant_base.span = variant_expr.span.clone();
                    &Expr::new_typed(ExprKind::Infix(Box::new(variant_expr.clone()), Op::Lt, Box::new(Expr::ident(&variant_name, &Type::Int))), Type::Bool)
                },
                _ => &Expr::new_typed(ExprKind::Bool(true), Type::Bool)
            };

            let method_context = MethodContext {
                name: m.name.clone(),
                post_conditions: post_conditions.clone(),
                variant_assertion: variant_assertion.clone(),
                global_variables_old_values: global_variables_old_values.clone()
            };

            // Get method's body
            let mut cmd = m.body.clone().unwrap().cmd;

            let mut symbol_table = HashSet::new();

            if let Some((span, msg)) = does_method_modify_unspecified_global_variables(
                &cmd,
                &specified_global_variables,
                &mut symbol_table
            ) {
                cx.error(span, msg);
                return Ok(())
            }

            match m.return_ty.clone() {
                None => {
                    let last_cmd = &Cmd::_return(&None);
                    cmd = Box::new(cmd.seq(last_cmd))
                },
                Some(_) => {
                    let mut expr = Expr::bool(false);
                    expr.span = m.name.span.clone();
                    let last_cmd = &Cmd::assert(&expr, "Method might not return");
                    cmd = Box::new(cmd.seq(last_cmd))
                }
            }

            // Encode it in IVL
            let ivl_encoding = cmd_to_ivlcmd(
                &cmd,
                &method_context,
                &LoopContext::empty()
            )?;

            ivl = ivl.seq(&ivl_encoding);

            let dsa = ivl_to_dsa(&ivl, &mut HashMap::new())?;

            // Calculate obligation and error message (if obligation is not
            // verified)
            let wp_list = wp_set(&dsa, vec![])?;
            for WeakestPrecondition{ expr, span, msg } in wp_list {
                // Convert obligation to SMT expression
                let soblig = expr.smt()?;

                // Run the following solver-related statements in a closed scope.
                // That is, after exiting the scope, all assertions are forgotten
                // from subsequent executions of the solver
                solver.scope(|solver| {
                    // Check validity of obligation
                    solver.assert(!soblig.as_bool()?)?;
                    // Run SMT solver on all current assertions
                    match solver.check_sat()? {
                        // If the obligations result not valid, report the error (on
                        // the span in which the error happens)
                        smtlib::SatResult::Sat => {
                            //println!("{}", format!("expr: {expr} span_start: {}  span_end: {}", span.start(), span.end()));
                            cx.error(span, format!("{msg}"));
                        }
                        smtlib::SatResult::Unknown => {
                            cx.warning(span, "{msg}: unknown sat result");
                        }
                        smtlib::SatResult::Unsat => (),
                    }
                    Ok(())
                })?;
            }
        }

        Ok(())
    }
}

fn does_method_modify_unspecified_global_variables(
    cmd: &Cmd,
    specified_global_variables: &HashSet<String>,
    symbol_table: &mut HashSet<String>
) -> Option<(Span, String)> {
    match &cmd.kind {
        CmdKind::Seq(c1, c2) => {
            if let Some(t) = does_method_modify_unspecified_global_variables(&c1, specified_global_variables, symbol_table) {
                return Some(t)
            }
            does_method_modify_unspecified_global_variables(&c2, specified_global_variables, symbol_table)
        }
        CmdKind::VarDefinition { name, .. } => {
            symbol_table.insert(name.ident.0.clone());
            None
        }
        CmdKind::Assignment { name, .. } => {
            //println!("Searching for {} in symbol table {:#?}", name, symbol_table);
            if symbol_table.contains(&name.ident.0) {
                return None
            }
            //println!("Searching for {} in global variables {:#?}", name, specified_global_variables);
            if specified_global_variables.contains(&name.ident.0) {
                return None
            }
            Some((cmd.span, String::from("Unspecified global variable is modified")))
        }
        CmdKind::Match { body } => {
            let mut last = None;
            for case in &body.cases {
                last = does_method_modify_unspecified_global_variables(&case.cmd, specified_global_variables, symbol_table);
                if let Some(t) = last {
                    return Some(t)
                }
            }
            last
        }
        CmdKind::Loop { body, .. } => {
            let mut last = None;
            for case in &body.cases {
                last = does_method_modify_unspecified_global_variables(&case.cmd, specified_global_variables, symbol_table);
                if let Some(t) = last {
                    return Some(t)
                }
            }
            last
        }
        CmdKind::MethodCall { name: Some(name), ..} => {
            if symbol_table.contains(&name.ident.0) {
                return None
            }
            if specified_global_variables.contains(&name.ident.0) {
                return None
            }
            Some((cmd.span, String::from("Unspecified global variable is modified")))
        }
        CmdKind::For { body, .. } => {
            does_method_modify_unspecified_global_variables(&body.cmd, specified_global_variables, symbol_table)
        }
        _ => None
    }
}

fn ivl_to_dsa(ivl: &IVLCmd, varmap: &mut HashMap<Ident, (Ident, Type)>) -> Result<IVLCmd> {
    match &ivl.kind {
        IVLCmdKind::Assignment { name, expr } => {
            // if there is any identifier in expr, replace them with the ones in map
            let dsa = replace_identifiers_with_recent_names_in_varmap(expr, varmap);
            // get new ident for name and update it in the map
            let new_ident = get_fresh_var_name(&name.ident);
            varmap.insert(name.ident.clone(), (new_ident.clone(), expr.ty.clone()));
            // assume new_ident == dsa
            Ok(assume_equality(
                &Expr::new_typed(ExprKind::Ident(new_ident), expr.ty.clone()),
                &dsa
            ))
        },
        IVLCmdKind::NonDet(ivl1, ivl2) => {
            let mut map1 = varmap.clone();
            let mut branch1 = ivl_to_dsa(ivl1, &mut map1)?;
            let mut map2 = varmap.clone();
            let mut branch2 = ivl_to_dsa(ivl2, &mut map2)?;
            // synchronize branches
            for (ident, (ver, ty)) in map1.clone() {
                if map2.contains_key(&ident) {
                    let new_ident = get_fresh_var_name(&ident);
                    varmap.insert(ident.clone(), (new_ident.clone(), ty.clone()));
                    branch1 = branch1.seq(&assume_equality(
                        &Expr::new_typed(ExprKind::Ident(new_ident), ty.clone()),
                        &Expr::new_typed(ExprKind::Ident(ver), ty.clone())
                    ))
                } else {
                    let new_ident = get_fresh_var_name(&ident);
                    branch2 = branch2.seq(&assume_equality(
                        &Expr::new_typed(ExprKind::Ident(ident), ty.clone()),
                        &Expr::new_typed(ExprKind::Ident(new_ident), ty.clone())
                    ))
                }
            }
            for (ident, (ver, ty)) in map2 {
                if map1.contains_key(&ident) {
                    if let Some((new_ident, _)) = varmap.get(&ident) {
                        branch2 = branch2.seq(&assume_equality(
                            &Expr::new_typed(ExprKind::Ident(new_ident.clone()), ty.clone()),
                            &Expr::new_typed(ExprKind::Ident(ver), ty.clone())
                        ))
                    }
                } else {
                    let new_ident = get_fresh_var_name(&ident);
                    branch1 = branch1.seq(&assume_equality(
                        &Expr::new_typed(ExprKind::Ident(ident), ty.clone()),
                        &Expr::new_typed(ExprKind::Ident(new_ident), ty.clone())
                    ))
                }
            }
            Ok(branch1.nondet(&branch2))
        },
        IVLCmdKind::Seq(ivl1, ivl2) => {
            Ok(ivl_to_dsa(ivl1, varmap)?.seq(&ivl_to_dsa(ivl2, varmap)?))
        },
        IVLCmdKind::Assert { condition, message } => {
            let dsa = replace_identifiers_with_recent_names_in_varmap(condition, varmap);
            Ok(IVLCmd::assert(&dsa, message))
        },
        IVLCmdKind::Assume { condition } => {
            let dsa = replace_identifiers_with_recent_names_in_varmap(condition, varmap);
            Ok(IVLCmd::assume(&dsa))
        },
        _ => panic!("Expected Assignment, NonDet, Seq, Assert, or Assume!")
    }
}

fn assume_equality(expr1: &Expr, expr2: &Expr) -> IVLCmd {
    IVLCmd::assume(
        &Expr::new_typed(
            ExprKind::Infix(
                Box::new(expr1.clone()),
                Op::Eq,
                Box::new(expr2.clone())
            ),
            Type::Bool
        )
    )
}

fn replace_identifiers_with_recent_names_in_varmap(expr: &Expr, varmap: &HashMap<Ident, (Ident, Type)>) -> Expr {
    let idents = extract_identifiers_from_expression(expr, vec![]);
    let mut dsa = expr.clone();
    for (ident, _) in idents {
        if let Some((replace, ty)) = varmap.get(&ident).cloned() {
            dsa = replace_in_expression(
                &dsa,
                &Name::ident(ident),
                &Expr::new_typed(ExprKind::Ident(replace), ty.clone()),
            );
        }
    }
    dsa
}

fn extract_identifiers_from_expression(expr: &Expr, ignored_quantified_identifiers: Vec<Ident>) -> Vec<(Ident, Type)> {
    match &expr.kind {
        ExprKind::Ident(id) => {
            if ignored_quantified_identifiers.contains(id) {
                vec![]
            } else {
                vec![(id.clone(), expr.clone().ty)]
            }
        },
        ExprKind::Infix(e1, _, e2) =>
            [
                extract_identifiers_from_expression(e1, ignored_quantified_identifiers.clone()),
                extract_identifiers_from_expression(e2, ignored_quantified_identifiers.clone())
            ].concat(),
        ExprKind::Prefix(_, e) =>
            extract_identifiers_from_expression(e, ignored_quantified_identifiers.clone()),
        ExprKind::Ite(e1, e2, e3) =>
            [
                extract_identifiers_from_expression(e1, ignored_quantified_identifiers.clone()),
                extract_identifiers_from_expression(e2, ignored_quantified_identifiers.clone()),
                extract_identifiers_from_expression(e3, ignored_quantified_identifiers.clone()),
            ].concat(),
        ExprKind::FunctionCall { args, .. } => {
            let mut result = vec![];
            for arg in args {
                result.push(extract_identifiers_from_expression(
                    arg, ignored_quantified_identifiers.clone()));
            }
            result.concat()
        },
        ExprKind::Quantifier(_q, vars, e) => {
            let mut ignored_quantified_identifiers = ignored_quantified_identifiers.clone();
            for var in vars {
                ignored_quantified_identifiers.push(var.name.ident.clone())
            }
            extract_identifiers_from_expression(e, ignored_quantified_identifiers)
        },
        _ => vec![]
    }
}

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd, method_context: &MethodContext, loop_context: &LoopContext) -> Result<IVLCmd> {
    let &Cmd { kind, span, .. } = &cmd;
    Ok(match kind {
        CmdKind::Assert { condition, message } =>
            IVLCmd::assert(condition, message),
        CmdKind::Assume { condition} =>
            IVLCmd::assume(condition),
        CmdKind::Seq(cmd1, cmd2) =>
            cmd_to_ivlcmd(cmd1, &method_context, loop_context)?.seq(
                &cmd_to_ivlcmd(cmd2, &method_context, loop_context)?),
        CmdKind::VarDefinition { name, ty: (_, typ), expr: None } =>
            havoc_to_ivl(name, typ),
        CmdKind::VarDefinition { name, expr:Some(value), ..  } =>
            insert_division_by_zero_assertions(value, span)?.seq(&IVLCmd::assign(name, value)),
        CmdKind::Assignment { name, expr } =>
            insert_division_by_zero_assertions(expr, span)?.seq(&IVLCmd::assign(name, expr)),
        CmdKind::Match {body} =>
            match_to_ivl(body, method_context, loop_context)?,
        CmdKind::Return { expr: Some(value)} =>
            insert_division_by_zero_assertions(value, span)?.seq(
                &return_to_ivl(Some(value), method_context)?
            ),
        CmdKind::Return { expr: None } =>
            return_to_ivl(None, method_context)?,
        CmdKind::MethodCall { name, args, method, fun_name } =>
            method_call_to_ivl(name, args, method, fun_name, method_context)?,
        CmdKind::Loop { invariants , variant, body: cases } =>
            loop_to_ivl(invariants,variant, cases, &method_context)?,
        CmdKind::For { name, range, invariants, variant, body } =>
            for_to_ivl(name, range, invariants, variant, body, method_context)?,
        CmdKind::Continue =>
            continue_to_ivl(loop_context)?,
        CmdKind::Break =>
            break_to_ivl(loop_context)?,
        _ => todo!("{:#?}", cmd.kind),
    })
}

fn break_to_ivl(loop_context: &LoopContext) -> Result<IVLCmd> {
    let mut result = IVLCmd::assert(&Expr::bool(true), "Congratulations it couldn't fail!");
    for invariant in loop_context.clone().invariants {
        let expr_without_broke = replace_broke_in_expression(&invariant.clone(), true);
        result = result.seq(&IVLCmd::assert(&expr_without_broke, "Invariant might not hold after break"));
    }
    result = result.seq(&IVLCmd::assume(&Expr::bool(false)));
    Ok(result)
}

fn continue_to_ivl(loop_context: &LoopContext) -> Result<IVLCmd> {
    let mut result = IVLCmd::assert(&Expr::bool(true), "Congratulations it couldn't fail!");
    for invariant in loop_context.clone().invariants {
        let expr_without_broke = replace_broke_in_expression(&invariant.clone(), false);
        result = result.seq(&IVLCmd::assert(&expr_without_broke, "Invariant might not hold after continue"));
    }
    result = result.seq(&IVLCmd::assert(&loop_context.variant_assertion, "Variant might not hold after continue"));
    result = result.seq(&IVLCmd::assume(&Expr::bool(false)));
    Ok(result)
}

fn replace_broke_in_expression(original_expression: &Expr, replace_value: bool) -> Expr {
    let mut result = match &original_expression.kind {
        ExprKind::Broke => Expr::bool(replace_value),
        ExprKind::Prefix(op, expr) => Expr::new_typed(
            ExprKind::Prefix(
                *op,
                Box::new(replace_broke_in_expression(expr, replace_value))
            ),
            original_expression.ty.clone()),
        ExprKind::Infix(lhs, op, rhs) => Expr::new_typed(
            ExprKind::Infix(
                Box::new(replace_broke_in_expression(lhs, replace_value)),
                *op,
                Box::new(replace_broke_in_expression(rhs, replace_value))
            ),
            original_expression.ty.clone()),
        ExprKind::Quantifier(quantifier, vars, expr) => Expr::new_typed(
            ExprKind::Quantifier(
                quantifier.clone(),
                vars.clone(),
                Box::new(replace_broke_in_expression(expr, replace_value))
            ),
            original_expression.ty.clone()),
        _ => original_expression.clone(),
    };
    result.span = original_expression.span;
    result
}

fn for_to_ivl(name: &Name, Range::FromTo(start, end): &Range, invariants: &Vec<Expr>, variant: &Option<Expr>, body: &Block, method_context: &MethodContext) -> Result<IVLCmd> {
    let is_bounded = check_if_bounded(start) && check_if_bounded(end);
    if is_bounded {
        return bounded_to_ivl(name, start, end, body, method_context);
    } else {
        return unbounded_to_ivl(name, start, end, invariants, variant, body, method_context);
    }
}

fn check_if_bounded(expr: &Expr) -> bool {
    return match expr.kind {
        ExprKind::Num(_value) => true,
        _ => false
    };
}

fn evaluate_bounded(expr: &Expr) -> i64 {
    return match expr.kind {
        ExprKind::Num(value) => value,
        _ => panic!("Was not bounded!")
    };
}

fn bounded_to_ivl(name: &Name, start: &Expr, end: &Expr, body: &Block, method_context: &MethodContext) -> Result<IVLCmd>{
    let start_value = evaluate_bounded(start);
    let end_value = evaluate_bounded(end);
    if start_value > end_value {
        panic!("Start value is higher than end value");
    }

    let mut result = IVLCmd::assign(name, &Expr::new_typed(ExprKind::Num(start_value), Type::Int));
    let translated_body = cmd_to_ivlcmd(&body.cmd, method_context, &LoopContext::empty())?;
    for i in 0..(end_value - start_value) {
        result = result.seq(&translated_body);
        result = result.seq(&IVLCmd::assign(name, &Expr::new_typed(ExprKind::Num(start_value + i + 1), Type::Int)));
    }

    return Ok(result);
}

fn unbounded_to_ivl(name: &Name, start: &Expr, end: &Expr, invariants: &Vec<Expr>, variant: &Option<Expr>, body: &Block, method_context: &MethodContext) -> Result<IVLCmd> {
    let iterator_invariant = Expr::new_typed(ExprKind::Infix(Box::new(Expr::new_typed(ExprKind::Ident(name.ident.clone()), Type::Int)), Op::Le, Box::new(end.clone())), Type::Bool);

    let for_condition = Expr::new_typed(ExprKind::Infix(Box::new(Expr::new_typed(ExprKind::Ident(name.ident.clone()), Type::Int)), Op::Lt, Box::new(end.clone())), Type::Bool);
    let iterator_increase = Cmd::assign(name, &Expr::new_typed(ExprKind::Infix(Box::new(Expr::ident(&name.ident, &Type::Int)), Op::Add, Box::new(Expr::new_typed(ExprKind::Num(1), Type::Int))), Type::Int));
    let body_as_cases = Cases { span: body.span, cases: vec![Case { condition: for_condition, cmd: (*body.cmd.clone()).seq(&iterator_increase) } ] };

    let mut combined_invariants = invariants.clone();
    combined_invariants.push(iterator_invariant.clone());
    let translation_to_loop = loop_to_ivl(&combined_invariants, variant, &body_as_cases, &method_context)?;

    return Ok(
        IVLCmd::assign(name, start)
        .seq(&translation_to_loop)
    );
}

fn return_to_ivl(expr: Option<&Expr>, method_context: &MethodContext) -> Result<IVLCmd> {
    // we model the return with the following:
    // assert method_post_conditions[result <- expr]
    // assume false
    let mut result = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    match expr {
        Some(return_value) => {
            for post_condition in method_context.post_conditions.clone() {
                let replaced_result = replace_result_in_expression(&post_condition, return_value);
                let replaced_old = replace_old_in_expression(&replaced_result, &method_context.global_variables_old_values);
                // assert method_post_conditions[result <- expr]
                result = result.seq(&IVLCmd::assert(&replaced_old, "Ensure might not hold"))
            }
        }
        None => {
            for post_condition in method_context.post_conditions.clone() {
                let replaced_old = replace_old_in_expression(&post_condition, &method_context.global_variables_old_values);
                //println!("replace_old {}", replaced_old);
                // assert method_post_conditions
                result = result.seq(&IVLCmd::assert(&replaced_old, "Ensure might not hold"))
            }
        }
    }
    // assume false
    result = result.seq(&IVLCmd::assume(&Expr::new_typed(ExprKind::Bool(false), Type::Bool)));
    return Ok(result)
}

fn loop_to_ivl(invariants: &Vec<Expr>, variant: &Option<Expr>, cases: &Cases, method_context: &MethodContext) -> Result<IVLCmd> {
    let mut result = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    let mut assert_seq_cmd = Cmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    for invariant in invariants {
        let expr_without_broke = replace_broke_in_expression(invariant, false);
        result = result.seq(&IVLCmd::assert(&expr_without_broke, "Invariant might not hold on entry"));
        assert_seq_cmd = assert_seq_cmd.seq(&Cmd::assert(&expr_without_broke, "Invariant might not be preserved"));
    }

    for case in cases.cases.clone() {
        let modified_variables = find_modified_variables(&case.cmd)?;
        for (name, typ) in modified_variables {
            result = result.seq(&havoc_to_ivl(&name, &typ));
        }
    }

    for invariant in invariants {
        let expr_without_broke = replace_broke_in_expression(invariant, false);
        result = result.seq(&IVLCmd::assume(&expr_without_broke))
    }

    let variant_assertion = match variant {
        Some(variant_expr) => {
            let variant_name = get_fresh_var_name(&Ident(String::from("variant")));
            let variant_assignment = IVLCmd::assign(&Name { span: variant_expr.span, ident: variant_name.clone() }, variant_expr);
            let mut variant_base = Expr::new_typed(ExprKind::Infix(Box::new(Expr::ident(&variant_name.clone(), &Type::Int)), Op::Ge, Box::new(Expr::num(0))), Type::Bool);
            variant_base.span = variant_expr.span.clone();
            result = result.seq(&variant_assignment).seq(&IVLCmd::assert(&variant_base, "Variant might not always be >= 0"));
            &Expr::new_typed(ExprKind::Infix(Box::new(variant_expr.clone()), Op::Lt, Box::new(Expr::ident(&variant_name, &Type::Int))), Type::Bool)
        },
        _ => &Expr::new_typed(ExprKind::Bool(true), Type::Bool)
    };

    let mut new_cases =  vec![];
    for case in cases.cases.clone() {
        new_cases.push(Case {
            condition: case.condition,
            cmd: 
                case.cmd
                .seq(&assert_seq_cmd)
                .seq(&Cmd::assert(variant_assertion, "Variant might not hold"))
                .seq(&Cmd::assume(&Expr::new_typed(ExprKind::Bool(false), Type::Bool)) // We need to ignore the post condition
            )
        })
    }

    let loop_context = &LoopContext {
        invariants: invariants.clone(),
        variant_assertion: variant_assertion.clone()
    };

    let mut body_translation = match_to_ivl(
        &Cases { cases: new_cases.clone(), span: cases.span.clone()},
        method_context,
        loop_context)?;

    // DFS for breaks and chain using none deterministic choices
    for case in cases.clone().cases {
        let break_paths = find_break_paths(&case.cmd, IVLCmd::nop(), method_context, loop_context)?;

        for break_path in break_paths {
            body_translation = body_translation.nondet(&break_path)
        }
    }
    

    result = result.seq(&body_translation);

    return Ok(result);
}

fn find_break_paths(command: &Cmd, context: IVLCmd, method_context: &MethodContext, loop_context: &LoopContext) -> Result<Vec<IVLCmd>> {
    return Ok(match &command.kind {
        CmdKind::Break => vec![context],
        CmdKind::Seq(cmd1, cmd2) => {
            let paths_in_cmd1 = find_break_paths(&cmd1, context.clone(), method_context, loop_context)?;
            let cmd1_to_context = cmd_to_ivlcmd(&cmd1, method_context, loop_context)?;
            let paths_in_cmd2 = find_break_paths(&cmd2, context.clone().seq(&cmd1_to_context), method_context, loop_context)?;
            vec![paths_in_cmd1, paths_in_cmd2].concat()
        }
        CmdKind::Match { body } => {
            let mut match_context = context.clone();
            let mut paths = Vec::new();
            for case in body.cases.clone() {
                let ivl_for_condition = IVLCmd::assume(&case.condition);
                let paths_for_case = find_break_paths(
                    &case.cmd, 
                    match_context.seq(&ivl_for_condition), 
                    method_context, 
                    loop_context)?;
                paths.extend(paths_for_case);
                match_context = match_context.seq(&IVLCmd::assume(&Expr::prefix(&case.condition, PrefixOp::Not)));
            }
            paths
        }
        _ => Vec::new(),
    });
}

fn find_modified_variables(cmd: &Cmd) -> Result<Vec<(Name, Type)>> {
    let &Cmd { kind, .. } = &cmd;
    Ok(match kind {
        CmdKind::Seq(cmd1, cmd2) => {
            [
                find_modified_variables(&cmd1)?,
                find_modified_variables(&cmd2)?
            ].concat()
        }
        CmdKind::VarDefinition { name, ty: (_, typ), expr: _ } =>
            vec![(name.clone(), typ.clone())],
        CmdKind::Assignment { name, expr } =>
            vec![(name.clone(), expr.ty.clone())],
        CmdKind::Match {body} => {
            let mut modified_variables = vec![];
            for case in body.cases.clone() {
                modified_variables.extend(find_modified_variables(&case.cmd)?);
            }
            modified_variables
        }
        CmdKind::MethodCall { name: Some(return_value), fun_name: _, method, .. } =>
            vec![(return_value.clone(), method.get().unwrap().return_ty.clone().unwrap().1)],
        CmdKind::Loop { variant: None, body, .. } => {
            let mut modified_variables = vec![];
            for case in body.cases.clone() {
                modified_variables.extend(find_modified_variables(&case.cmd)?);
            }
            modified_variables
        },
        _ => vec![],
    })
}

fn method_call_to_ivl(result_name: &Option<Name>, args: &Vec<Expr>, method: &MethodRef, fun_name: &Name, method_context: &MethodContext) -> Result<IVLCmd> {
    // zero divisions assertions
    let mut result = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    let arc = method.get().unwrap();

    let mut return_value = None;

    if let Some(result_name) = result_name {
        if let Some((span, ty)) = &arc.return_ty {
            return_value = Some((result_name, span, ty))
        }
    }

    // Save prestate of arguments
    let mut names_map = vec![];
    for (arg, var) in zip(args, &arc.args) {
        result = result.seq(&insert_division_by_zero_assertions(arg, &arg.span.clone())?);
        let new_name = Name { ident: get_fresh_var_name(&var.name.ident), span: arg.span };
        result = result.seq(&IVLCmd::assign(&new_name, arg));
        names_map.push((var.clone(), new_name.ident));
    }

    // Save prestate of global variables
    let mut global_variables_values_before_call = HashMap::new();
    for (name, ty) in method.get().unwrap().modifies() {
        let global_variable_old_name = get_fresh_var_name(&name.ident.clone());
        global_variables_values_before_call.insert(name.ident.clone(), (global_variable_old_name.clone(), ty.clone()));
        result = result.seq(&IVLCmd::assign(
            &Name { ident: global_variable_old_name, span: name.span.clone() },
            &Expr::ident(&name.ident.clone(), ty)
        ))
    }

    // Make sure variant holds
    if fun_name.ident == method_context.name.ident {
        let mut updated_variant_assertion = method_context.variant_assertion.clone();
        for (old_var, new_name) in names_map.clone() {
            updated_variant_assertion = replace_in_expression(
                &updated_variant_assertion,
                &old_var.name,
                &Expr::new_typed(ExprKind::Ident(new_name), old_var.ty.1)
            );
        }
        result = result.seq(&IVLCmd::assert(&updated_variant_assertion, "Variant might not hold"));
    }

    // pre-condition of the method
    let requires = arc.requires();

    // assert preconditions
    for method_pre_condition in requires {
        let mut updated_pre_cond = method_pre_condition.clone();
        for (old_var, new_name) in names_map.clone() {
            updated_pre_cond = replace_in_expression(
                &updated_pre_cond,
                &old_var.name,
                &Expr::new_typed(ExprKind::Ident(new_name), old_var.ty.1)
            );
        }

        result = result.seq(&IVLCmd::assert(&updated_pre_cond, "Requires might not hold"));
    }


    // havoc result variable if exists
    if let Some((return_name, _span, ty)) = return_value {
        result = result.seq(&havoc_to_ivl(return_name, ty))
    }

    // Havoc modified globals variables
    for (modified_global_variable, ty) in method.get().unwrap().modifies() {
        result = result.seq(&havoc_to_ivl(modified_global_variable, ty));
    }

    // assert post-conditions of the method
    let ensures = arc.ensures();
    for method_post_condition in ensures {
        let mut updated_post_cond = method_post_condition.clone();
        for (old_var, new_name) in names_map.clone() {
            updated_post_cond = replace_in_expression(
                &updated_post_cond,
                &old_var.name,
                &Expr::ident(&new_name, &old_var.ty.1)
            );
        }
        if let Some((return_name, _span, ty)) = return_value {
            updated_post_cond = replace_result_in_expression(
                &updated_post_cond,
                &Expr::new_typed(ExprKind::Ident(return_name.ident.clone()), ty.clone())
            );
        }
        updated_post_cond = replace_old_in_expression(
            &updated_post_cond,
            &global_variables_values_before_call
        );
        result = result.seq(&IVLCmd::assume(&updated_post_cond));
    }

    return Ok(result)
}

fn insert_division_by_zero_assertions(expr: &Expr, span: &Span) -> Result<IVLCmd> {
    let divisors = extract_division_assertions(expr)?;
    let mut assertion = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    if divisors.is_empty() {
        return Ok(assertion.clone());
    }
    for divisor in divisors {
        assertion = assertion.seq(&IVLCmd::assert_with_span(
            &divisor,
            "Possible division by zero!",
            &span)
        );
    }
    return Ok(assertion);
}

fn extract_division_assertions(expr: &Expr) -> Result<Vec<Expr>> {
    Ok(match &expr.kind {
        ExprKind::Prefix(_op, e) => extract_division_assertions(e)?,
        ExprKind::Infix(e1, op, e2) if op.clone() == Op::Div => {
            let mut result = extract_division_assertions(e1)?.clone();
            result.extend(extract_division_assertions(e2)?);
            result.push(
                Expr::new_typed(
                    ExprKind::Infix(
                        e2.clone(),
                        Op::Ne,
                        Box::new(Expr::num(0))
                    ),
                Type::Bool
                )
            );
            result
        }
        ExprKind::Infix(e1, _op, e2) => {
            let mut result = extract_division_assertions(e1)?.clone();
            result.extend(extract_division_assertions(e2)?);
            result
        }
        ExprKind::Ite(condition, e1, e2) => {
            let mut result = extract_division_assertions(condition)?.clone();
            let left = extract_division_assertions(e1)?;
            for expr in left {
                let mut new_expr = Expr::new_typed(
                    ExprKind::Infix(condition.clone(), Op::Imp, Box::new(expr.clone())),
                    Type::Bool
                );
                new_expr.span = expr.span.clone();
                result.push(
                    new_expr
                );
            }

            let right = extract_division_assertions(e2)?;
            for expr in right {
                let mut new_expr = Expr::new_typed(
                    ExprKind::Infix(
                        Box::new(Expr::new_typed(ExprKind::Prefix(PrefixOp::Not, condition.clone()), Type::Bool)),
                        Op::Imp,
                        Box::new(expr.clone())),
                    Type::Bool);
                new_expr.span = expr.span.clone();
                result.push(
                    new_expr
                );
            }
            result
        }
        ExprKind::FunctionCall { fun_name:_, args, function:_} => {
            let mut args_divisors = vec![];
            for arg in args {
                args_divisors.extend(extract_division_assertions(arg)?);
            }
            args_divisors
        },
        _ => vec![]
    })
}

fn match_to_ivl(body: &Cases, method_context: &MethodContext, loop_context: &LoopContext) -> Result<IVLCmd> {
    if body.cases.len() == 0 {
        return Ok(IVLCmd::nop())
    }
    let first_case = body.cases[0].clone();
    let cmd_b: IVLCmd =
        insert_division_by_zero_assertions(&first_case.condition, &first_case.condition.span)?.seq(
            &IVLCmd::assume(&first_case.condition).seq(
                &cmd_to_ivlcmd(&first_case.cmd, &method_context, loop_context)?
            )
        );
    let assume_not_b = IVLCmd::assume(
        &Expr::new_typed(ExprKind::Prefix(PrefixOp::Not,Box::new(first_case.condition.clone())), Type::Bool));

    if body.cases.len() == 1 {
        return Ok(cmd_b.nondet(&assume_not_b));
    }
    let new_body = Cases{ span: body.span, cases: body.cases[1 .. body.cases.len()].to_vec() };
    let cmd_not_b: IVLCmd = assume_not_b.seq(&match_to_ivl(&new_body, method_context, loop_context)?);
    return Ok(cmd_b.nondet(&cmd_not_b));
}

fn havoc_to_ivl(name: &Name, typ: &Type) -> IVLCmd {
    return IVLCmd::assign(name, &Expr::new_typed(ExprKind::Ident(get_fresh_var_name(&name.ident)), typ.clone()));
}

fn wp_set(ivl: &IVLCmd, post_conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => wp_set_assert(condition, message, post_conditions),
        IVLCmdKind::Assume { condition } => wp_set_assume(condition, post_conditions),
        IVLCmdKind::Seq(cmd1, cmd2) => wp_set_seq(cmd1, cmd2, post_conditions),
        IVLCmdKind::NonDet(cmd1, cmd2) => wp_set_nondet(cmd1, cmd2, post_conditions),
        _ => todo!("Expected Assert, Assume, Seq, or NonDet!"),
    }
}

fn wp_set_nondet(cmd1: &Box<IVLCmd>, cmd2: &Box<IVLCmd>, post_condition: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    let wp_set1 = wp_set(cmd1, post_condition.clone())?;
    let wp_set2 = wp_set(cmd2, post_condition.clone())?;
    return Ok([wp_set1, wp_set2].concat());
}

fn wp_set_assert(condition: &Expr, message: &String, post_conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    // for error localization we consider "assert H;" to be equivalent to "assert H; assume H;"
    return Ok([wp_set_assume(condition, post_conditions)?, vec![WeakestPrecondition { expr: condition.clone(), span: condition.span, msg: message.clone() }]].concat());
}

fn wp_set_assume(condition: &Expr, post_conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    let mut new_conditions: Vec<WeakestPrecondition> = vec![];
    for WeakestPrecondition { expr, span, msg } in post_conditions {
        let new_condition = Expr::new_typed(ExprKind::Infix(Box::new(condition.clone()), Op::Imp, Box::new(expr.clone())), Type::Bool);
        new_conditions.push(WeakestPrecondition { expr: new_condition, span: span, msg: msg });
    }
    return Ok(new_conditions);
}

fn wp_set_seq(cmd1: &Box<IVLCmd>, cmd2: &Box<IVLCmd>, post_condition: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    let wp_set2 = wp_set(cmd2, post_condition)?;
    let wp_set1 = wp_set(&cmd1, wp_set2)?;
    return Ok(wp_set1);
}

// f (e, i, v) -> e[i <- v]
fn replace_in_expression(original_expression: &Expr, identifier: &Name, replace_with_identifier: &Expr) -> Expr {
    let mut result = match &original_expression.kind {
        ExprKind::Ident(name) if name.0 == identifier.ident.0 => replace_with_identifier.clone(),
        ExprKind::Prefix(op, expr) => Expr::new_typed(
            ExprKind::Prefix(
                *op, 
                Box::new(replace_in_expression(expr, identifier, replace_with_identifier))
            ),
            original_expression.ty.clone()),
        ExprKind::Infix(lhs, op, rhs) => Expr::new_typed(
            ExprKind::Infix(
                Box::new(replace_in_expression(lhs, identifier, replace_with_identifier)),
                *op, 
                Box::new(replace_in_expression(rhs, identifier, replace_with_identifier))
            ),
            original_expression.ty.clone()),
        ExprKind::Quantifier(_quantifier, variables, expr) => {
            if (variables.into_iter().map(|x| x.name.ident.0.clone()).collect::<String>()).contains(&identifier.ident.0) {
                return original_expression.clone();
            }
            return replace_in_expression(expr, identifier, replace_with_identifier)
        } 
        _ => original_expression.clone(),
    };
    result.span = original_expression.span;
    result
}

fn replace_result_in_expression(original_expression: &Expr, replace_expression: &Expr) -> Expr {
    let mut result = match &original_expression.kind {
        ExprKind::Result => replace_expression.clone(),
        ExprKind::Prefix(op, expr) => Expr::new_typed(
            ExprKind::Prefix(
                *op,
                Box::new(replace_result_in_expression(expr, replace_expression))
            ),
            original_expression.ty.clone()),
        ExprKind::Infix(lhs, op, rhs) => Expr::new_typed(
            ExprKind::Infix(
                Box::new(replace_result_in_expression(lhs, replace_expression)),
                *op,
                Box::new(replace_result_in_expression(rhs, replace_expression))
            ),
            original_expression.ty.clone()),
        ExprKind::Quantifier(quantifier, vars, expr) => Expr::new_typed(
            ExprKind::Quantifier(
                quantifier.clone(),
                vars.clone(),
                Box::new(replace_result_in_expression(expr, replace_expression))
            ),
            original_expression.ty.clone()),
        _ => original_expression.clone(),
    };
    result.span = original_expression.span;
    result
}

fn replace_old_in_expression(original_expression: &Expr, global_variables_old_values: &HashMap<Ident, (Ident, Type)>) -> Expr {
    let mut result = match &original_expression.kind {
        ExprKind::Old(Name { ident, .. }) => {
            if let Some((new_ident, ty)) = global_variables_old_values.get(ident) {
                Expr::ident(new_ident, ty)
            } else {
                panic!("method can not modify this global variable")
            }
        },
        ExprKind::Prefix(op, expr) => Expr::new_typed(
            ExprKind::Prefix(
                *op,
                Box::new(crate::replace_old_in_expression(expr, global_variables_old_values))
            ),
            original_expression.ty.clone()),
        ExprKind::Infix(lhs, op, rhs) => Expr::new_typed(
            ExprKind::Infix(
                Box::new(crate::replace_old_in_expression(lhs, global_variables_old_values)),
                *op,
                Box::new(crate::replace_old_in_expression(rhs, global_variables_old_values))
            ),
            original_expression.ty.clone()),
        ExprKind::Quantifier(quantifier, vars, expr) => Expr::new_typed(
            ExprKind::Quantifier(
                quantifier.clone(),
                vars.clone(),
                Box::new(crate::replace_old_in_expression(expr, global_variables_old_values))
            ),
            original_expression.ty.clone()),
        _ => original_expression.clone(),
    };
    result.span = original_expression.span;
    result
}