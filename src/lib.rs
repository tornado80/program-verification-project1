pub mod ivl;
mod ivl_ext;

use std::vec;
use std::collections::{HashMap, HashSet};
use uuid::Uuid;
use std::iter::zip;
use ivl::{IVLCmd, IVLCmdKind, WeakestPrecondition};
use slang::ast::{Block, Cmd, CmdKind, Expr, ExprKind, Ident, MethodRef, Name, Op, Range, Type};
use slang_ui::prelude::*;
use slang_ui::prelude::slang::ast::{Cases, PrefixOp, Case, Quantifier, Method, Specification, Function};
use slang_ui::prelude::slang::{Span};
use slang_ui::prelude::slang::smt::SmtError::Smt;
use slang_ui::prelude::smtlib::backend::z3_binary::Z3Binary;
use slang_ui::prelude::smtlib::funs::Fun;
use slang_ui::prelude::smtlib::{Error, SatResult, Solver};
use slang_ui::prelude::smtlib::sorts::Sort;
use slang_ui::prelude::smtlib::terms::Dynamic;

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

        for d in file.domains() {
            for f in d.functions() {
                let mut vars = Vec::new();
                for arg in &f.args {
                    vars.push(Sort::new(type_to_string(&arg.ty.1)))
                }
                solver.declare_fun(&Fun::new(
                    f.name.to_string(),
                    vars,
                    Sort::new(type_to_string(&f.return_ty.1))
                ))?
            }

            for a in d.axioms() {
                let axiom = a.expr.smt()?;
                solver.assert(axiom.as_bool()?)?
            }
        }

        for f in file.functions() {
            let mut vars = Vec::new();
            for arg in &f.args {
                vars.push(Sort::new(type_to_string(&arg.ty.1)))
            }
            solver.declare_fun(&Fun::new(
                f.name.to_string(),
                vars,
                Sort::new(type_to_string(&f.return_ty.1))
            ))?;
        }

        for f in file.functions() {
            let mut std_args: Vec<Expr> = Vec::new();
            for arg in &f.args {
                std_args.push(Expr::ident(&arg.name.ident, &arg.ty.1))
            }

            let mut preconditions = Expr::bool(true);
            for precondition in f.requires() {
                preconditions = preconditions.and(precondition)
            }

            let mut body = Expr::bool(true);
            if let Some(b) = &f.body {
                body = Expr::call(
                    f.name.clone(),
                    std_args.clone(),
                    file.get_function_ref(f.name.ident.clone())
                ).op(Op::Eq, b)
            }



            // add as axiom
            /*
            function foo (x:T) : S
                axiom {
                    forall x:T :: F -> (foo (x) == (e) and G[result := foo(x)])
                }
            */
            let mut post_conditions = Expr::bool(true);
            for post_condition in f.ensures() {
                post_conditions = post_conditions.and(
                    &replace_result_in_expression(
                        post_condition,
                        &Expr::call(
                            f.name.clone(),
                            std_args.clone(),
                            file.get_function_ref(f.name.ident.clone())
                        ))
                );
            }
            let axiom = Expr::quantifier(
                Quantifier::Forall,
                &f.args[..],
                &preconditions.imp(
                    &body.and(
                        &post_conditions
                    )
                )
            );

            if let Ok(_) = does_function_body_comply_with_postconditions_in_isolated_scope(
                &f, &body, &preconditions, &post_conditions, &std_args, &file, cx, &mut solver) {
                solver.assert(axiom.smt()?.as_bool()?)?;
            }
        }

        // Iterate methods
        for m in file.methods() {
            if let None = m.body {
                continue;
            }
            let _ = verify_method(&m, cx, &mut solver);
        }

        Ok(())
    }
}

fn does_function_body_comply_with_postconditions_in_isolated_scope(
    f: &Function,
    body: &Expr,
    preconditions: &Expr,
    post_conditions: &Expr,
    std_args: &Vec<Expr>,
    file: &slang::SourceFile,
    cx: &mut slang_ui::Context,
    solver: &mut Solver<Z3Binary>
) -> Result<(), Error> {
    let _axiom_only_body = Expr::quantifier(
        Quantifier::Forall,
        &f.args[..],
        &preconditions.imp(
            body
        )
    );

    let axiom_only_post_conditions = Expr::quantifier(
        Quantifier::Forall,
        &f.args[..],
        &preconditions.imp(
            post_conditions
        )
    );


    // add checker method
    /*
    method check foo (x:T) returns ( result : S)
        requires F
        ensures G
        ensures result == foo (x)
        { return e }
    */
    if let Some(b) = &f.body {
        let method_ensures_post_conditions = Method {
            name: Name::ident(get_fresh_var_name(&f.name.ident)),
            args: f.args.clone(),
            return_ty: Some(f.return_ty.clone()),
            span: f.span.clone(),
            specifications: f.specifications.clone(),
            variant: None,
            body: Some(Block {
                cmd: Box::new(Cmd::_return(&Some(b.clone()))),
                span: b.span.clone()
            })
        };
        //specifications.push(ensures_body);
        let mut requires: Vec<Specification> = Vec::new();
        for specification in &f.specifications {
            if let Specification::Requires { .. } = specification {
                requires.push(specification.clone());
            }
        }
        let ensures_body = Specification::Ensures {
            expr: Expr::result(&f.return_ty.1).op(Op::Eq, &Expr::call(
                f.name.clone(),
                std_args.clone(),
                file.get_function_ref(f.name.ident.clone())
            )
            ),
            span: f.name.span
        };
        requires.push(ensures_body);
        let _method_ensures_body = Method {
            name: Name::ident(get_fresh_var_name(&f.name.ident)),
            args: f.args.clone(),
            return_ty: Some(f.return_ty.clone()),
            span: f.span.clone(),
            specifications: requires.clone(),
            variant: None,
            body: Some(Block {
                cmd: Box::new(Cmd::_return(&Some(b.clone()))),
                span: b.span.clone()
            })
        };
        //println!("Axiom only body: {:#?}", axiom_only_body.to_string());
        //println!("Method only body: {:#?}", method_ensures_body);
        /*
        let result1 = solver.scope(|solver| {
            solver.assert(expr_to_smt(&axiom_only_body)?.as_bool()?)?;
            verify_method(&method_ensures_body, cx, solver)
        });
        */

        //println!("Axiom only post_conditions: {:#?}", axiom_only_post_conditions.to_string());
        //println!("Method post conditions: {:#?}", method_ensures_post_conditions);
        return solver.scope(|solver| {
            solver.assert(expr_to_smt(&axiom_only_post_conditions)?.as_bool()?)?;
            verify_method(&method_ensures_post_conditions, cx, solver)
        });
        /*
        match (result1, result2) {
            (Ok(_), Ok(_)) => (),
            (Err(e), Ok(_)) => {
                //println!("Ensure body failed {e}");
                return Err(e) },
            (Ok(_), Err(e)) => {
                //println!("Ensure post conditions failed {e}");
                return Err(e) }
            (Err(_e1), Err(_e2)) => {
                //println!("Both failed {e1} {e2}");
            }
        }

         */
    }
    Ok(())
}

fn expr_to_smt(expr: &Expr) -> Result<Dynamic, Error> {
    match expr.smt() {
        Ok(oblig) => Ok(oblig),
        Err(Smt(e)) => Err(e),
        Err(e) => Err(Error::Smt(e.to_string(), expr.to_string()))
    }
}

fn verify_method(m: &Method, cx: &mut slang_ui::Context, solver: &mut Solver<Z3Binary>) -> Result<(), Error> {
    //println!("Checking method {}", m.name);
    // Get method's preconditions;
    let pres = m.requires();
    // Merge them into a single condition
    let pre = pres
        .cloned()
        .reduce(|a, b| a & b)
        .unwrap_or(Expr::bool(true));
    // Convert the expression into an SMT expression
    let spre = expr_to_smt(&pre)?;
    // Assert precondition
    // Why do we assert the preconditions?
    // Reason:
    // We are interested in the validity of each of the following predicates in the set
    // because we are "assuming the preconditions":
    // {pre_condition -> wp_predicate : forall wp_predicate in wp_list(body)[post_conditions]}
    // However, we check for satisfiability of !(precondition -> wp_predicate)
    // which is equivalent to !(!precondition or wp_predicate) == precondition and !wp_predicate
    // Therefore we assert the precondition and later on assert the negation of each of the wp_predicate's
    //println!("Spre: {:#?}", spre);
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
        specified_global_variables.insert(name.to_string());
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
            variant_base.span = variant_expr.span.clone();
            ivl = ivl.seq(&variant_assignment).seq(&IVLCmd::assert(&variant_base, "Method variant might not be non-negative on entry"));
            variant_base.span = variant_expr.span.clone();
            &Expr::new_typed(ExprKind::Infix(Box::new(variant_expr.clone()), Op::Lt, Box::new(Expr::ident(&variant_name, &Type::Int))), Type::Bool)
        },
        None => &Expr::new_typed(ExprKind::Bool(true), Type::Bool)
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

    for arg in &m.args {
        symbol_table.insert(arg.name.to_string());
    }

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
            let mut last_cmd = Cmd::_return(&Some(Expr::result(&Type::Unresolved)));
            last_cmd.span = m.name.span.clone();
            cmd = Box::new(cmd.seq(&last_cmd))
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
    //println!("IVL:\n{:#?}", ivl);

    let dsa = ivl_to_dsa(&ivl, &mut HashMap::new())?;


    //println!("Method {} IVL {:#?}", m.name.to_string(), ivl.to_string());

    // Calculate obligation and error message (if obligation is not
    // verified)
    let wp_list = wp_set(&dsa, vec![])?;

    let mut res = Ok(());

    for WeakestPrecondition{ expr, span, msg } in wp_list {
        // Convert obligation to SMT expression
        let soblig = expr_to_smt(&expr)?;

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
                    cx.error(span, format!("{}", msg));
                    res = Err(Error::UnexpectedSatResult{expected: SatResult::Unsat, actual: SatResult::Sat});
                }
                smtlib::SatResult::Unknown => {
                    cx.error(span, format!("{msg}"));
                    res = Err(Error::UnexpectedSatResult{expected: SatResult::Unsat, actual: SatResult::Unknown});
                }
                smtlib::SatResult::Unsat => (),
            }
            Ok(())
        })?;
    }
    res
}

fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::Domain { name, .. } => name.to_string(),
        t => t.to_string()
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
            if symbol_table.contains(&name.to_string()) {
                return Some((name.span.clone(), format!("Redeclaration of variable {} is not allowed", &name.to_string())));
            }
            symbol_table.insert(name.to_string());
            None
        }
        CmdKind::Assignment { name, .. } => {
            //println!("Searching for {} in symbol table {:#?}", name, symbol_table);
            if symbol_table.contains(&name.to_string()) {
                return None
            }
            //println!("Searching for {} in global variables {:#?}", name, specified_global_variables);
            if specified_global_variables.contains(&name.to_string()) {
                return None
            }
            Some((cmd.span, format!("Variable {} is modified but not declared in the current scope. If it is a global variable, consider annotating the method.", name.to_string())))
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
        CmdKind::MethodCall { name, method, ..} => {
            if let Some(name) = name {
                if symbol_table.contains(&name.to_string()) {
                    return None
                }
                if specified_global_variables.contains(&name.to_string()) {
                    return None
                }
                return Some((cmd.span, format!("Variable {} is modified but not declared in the current scope. If it is a global variable, consider annotating the method.", name.to_string())))
            }
            for (variable_modified_by_called_method, _) in method.get()?.modifies() {
                if !specified_global_variables.contains(&variable_modified_by_called_method.ident.to_string()) {
                    return Some((cmd.span.clone(), format!("Global variable {} is modified by the called method but is not annotated in the current method as a modified global variable.", variable_modified_by_called_method.ident.to_string())));
                }
            }
            None
        }
        CmdKind::For { body, .. } => {
            does_method_modify_unspecified_global_variables(&body.cmd, specified_global_variables, symbol_table)
        }
        _ => None
    }
}

fn ivl_to_dsa(ivl: &IVLCmd, varmap: &mut HashMap<Ident, (Ident, Type)>) -> Result<IVLCmd, Error> {
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
fn cmd_to_ivlcmd(cmd: &Cmd, method_context: &MethodContext, loop_context: &LoopContext) -> Result<IVLCmd, Error> {
    let &Cmd { kind, span, .. } = &cmd;
    Ok(match kind {
        CmdKind::Assert { condition, message } =>
            IVLCmd::assert(&replace_old_in_expression(condition, &method_context.global_variables_old_values), message),
        CmdKind::Assume { condition} =>
            IVLCmd::assume(&replace_old_in_expression(condition, &method_context.global_variables_old_values)),
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
                &return_to_ivl(Some(value), span, method_context)?
            ),
        CmdKind::Return { expr: None } =>
            return_to_ivl(None, span, method_context)?,
        CmdKind::MethodCall { name, args, method, fun_name } =>
            method_call_to_ivl(name, args, span, method, fun_name, method_context)?,
        CmdKind::Loop { invariants , variant, body: cases } =>
            loop_to_ivl(invariants,variant, cases, &method_context)?,
        CmdKind::For { name, range, invariants, variant, body } =>
            for_to_ivl(name, range, invariants, variant, body, method_context)?,
        CmdKind::Continue =>
            continue_to_ivl(span, loop_context)?,
        CmdKind::Break =>
            break_to_ivl(span, loop_context)?,
        _ => todo!("{:#?}", cmd.kind),
    })
}

fn break_to_ivl(span: &Span, loop_context: &LoopContext) -> Result<IVLCmd, Error> {
    let mut result = IVLCmd::assert(&Expr::bool(true), "Congratulations it couldn't fail!");
    for invariant in loop_context.clone().invariants {
        let mut expr_without_broke = replace_broke_in_expression(&invariant.clone(), true);
        expr_without_broke.span = span.clone();
        result = result.seq(&IVLCmd::assert(
            &expr_without_broke,
            &format!("Invariant {} might not hold after break", invariant.to_string()),
        ));
    }
    result = result.seq(&IVLCmd::assume(&Expr::bool(false)));
    Ok(result)
}

fn continue_to_ivl(span: &Span, loop_context: &LoopContext) -> Result<IVLCmd, Error> {
    let mut result = IVLCmd::assert(&Expr::bool(true), "Congratulations it couldn't fail!");
    for invariant in loop_context.clone().invariants {
        let mut expr_without_broke = replace_broke_in_expression(&invariant.clone(), false);
        expr_without_broke.span = span.clone();
        result = result.seq(&IVLCmd::assert(
            &expr_without_broke,
            &format!("Loop invariant {} might not hold after continue", invariant.to_string())
        ));
    }
    let mut variant_assertion = loop_context.variant_assertion.clone();
    variant_assertion.span = span.clone();
    result = result.seq(&IVLCmd::assert(
        &variant_assertion,
        "Loop variant might not be decreased before continue"));
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
        ExprKind::FunctionCall { fun_name, args, function } => {
            let mut replaced_args = Vec::new();
            for arg in args {
                replaced_args.push(replace_broke_in_expression(arg, replace_value));
            }
            Expr::call(fun_name.clone(), replaced_args, function.clone())
        }
        _ => original_expression.clone(),
    };
    result.span = original_expression.span;
    result
}

fn for_to_ivl(name: &Name, Range::FromTo(start, end): &Range, invariants: &Vec<Expr>, variant: &Option<Expr>, body: &Block, method_context: &MethodContext) -> Result<IVLCmd, Error> {
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

fn bounded_to_ivl(name: &Name, start: &Expr, end: &Expr, body: &Block, method_context: &MethodContext) -> Result<IVLCmd, Error>{
    let start_value = evaluate_bounded(start);
    let end_value = evaluate_bounded(end);
    if start_value > end_value {
        return Ok(IVLCmd::nop());
    }

    let mut result = IVLCmd::assign(name, &Expr::new_typed(ExprKind::Num(start_value), Type::Int));
    let translated_body = cmd_to_ivlcmd(&body.cmd, method_context, &LoopContext::empty())?;
    for i in 0..(end_value - start_value) {
        result = result.seq(&translated_body);
        result = result.seq(&IVLCmd::assign(name, &Expr::new_typed(ExprKind::Num(start_value + i + 1), Type::Int)));
    }

    return Ok(result);
}

fn unbounded_to_ivl(name: &Name, start: &Expr, end: &Expr, invariants: &Vec<Expr>, variant: &Option<Expr>, body: &Block, method_context: &MethodContext) -> Result<IVLCmd, Error> {
    let mut iterator_invariant = Expr::new_typed(ExprKind::Infix(Box::new(Expr::new_typed(ExprKind::Ident(name.ident.clone()), Type::Int)), Op::Le, Box::new(end.clone())), Type::Bool);
    iterator_invariant = iterator_invariant.and(&Expr::op(&Expr::ident(&name.ident, &Type::Int), Op::Ge, start));

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

fn return_to_ivl(expr: Option<&Expr>, span: &Span, method_context: &MethodContext) -> Result<IVLCmd, Error> {
    // we model the return with the following:
    // assert method_post_conditions[result <- expr]
    // assume false
    let mut result = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    match expr {
        // CAVEAT: the following case is only for the last artificial "return;" added to the end of methods
        // that do not return anything. Note that result can not be used in the body of methods or
        // can not be returned. It is only for specification of ensures. We are artificially returning
        // result to be able to catch this specific return and set the correct span here
        Some(Expr { kind: ExprKind::Result, .. }) => {
            for post_condition in method_context.post_conditions.clone() {
                let mut replaced_old = replace_old_in_expression(&post_condition, &method_context.global_variables_old_values);
                replaced_old.span = post_condition.span.clone();
                //println!("replace_old {}", replaced_old);
                // assert method_post_conditions
                result = result.seq(&IVLCmd::assert(
                    &replaced_old,
                    &format!("Ensure {} might not hold", post_condition.to_string())
                ))
            }
        }
        Some(return_value) => {
            for post_condition in method_context.post_conditions.clone() {
                let replaced_result = replace_result_in_expression(&post_condition, return_value);
                let mut replaced_old = replace_old_in_expression(&replaced_result, &method_context.global_variables_old_values);
                replaced_old.span = span.clone();
                // assert method_post_conditions[result <- expr]
                result = result.seq(&IVLCmd::assert(
                    &replaced_old,
                    &format!("Ensure {} might not hold", post_condition.to_string())
                ))
            }
        }
        None => {
            for post_condition in method_context.post_conditions.clone() {
                let mut replaced_old = replace_old_in_expression(&post_condition, &method_context.global_variables_old_values);
                replaced_old.span = span.clone();
                //println!("replace_old {}", replaced_old);
                // assert method_post_conditions
                result = result.seq(&IVLCmd::assert(
                    &replaced_old,
                    &format!("Ensure {} might not hold", post_condition.to_string())
                ))
            }
        }
    }
    // assume false
    result = result.seq(&IVLCmd::assume(&Expr::new_typed(ExprKind::Bool(false), Type::Bool)));
    return Ok(result)
}

fn loop_to_ivl(invariants: &Vec<Expr>, variant: &Option<Expr>, cases: &Cases, method_context: &MethodContext) -> Result<IVLCmd, Error> {
    let mut result = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");

    match variant {
        Some(variant_expr) => {
            let mut variant_entry_assertion = IVLCmd::assert(&Expr::op(variant_expr, Op::Ge, &Expr::num(0)), "Loop variant might not be non-negative on entry");
            variant_entry_assertion.span = variant_expr.span;
            result = result.seq(&variant_entry_assertion);
        }
        _ => {}
    }

    let mut loop_invariants_assertions: Vec<(Expr, Expr)> = Vec::new();
    for invariant in invariants {
        let expr_without_broke = replace_broke_in_expression(invariant, false);
        let expr_without_old = replace_old_in_expression(&expr_without_broke, &method_context.global_variables_old_values);
        result = result.seq(&IVLCmd::assert(
            &expr_without_old,
            &format!("Loop invariant {} might not hold on entry", invariant.to_string())));
        loop_invariants_assertions.push((invariant.clone(), expr_without_old.clone()));
    }

    for case in cases.cases.clone() {
        let modified_variables = find_modified_variables(&case.cmd)?;
        for (name, typ) in modified_variables {
            result = result.seq(&havoc_to_ivl(&name, &typ));
        }
    }

    for invariant in invariants {
        let expr_without_broke = replace_broke_in_expression(invariant, false);
        let expr_without_old = replace_old_in_expression(&expr_without_broke, &method_context.global_variables_old_values);
        result = result.seq(&IVLCmd::assume(&expr_without_old))
    }

    let variant_assertion = match variant {
        Some(variant_expr) => {
            let variant_name = get_fresh_var_name(&Ident(String::from("variant")));
            let variant_assignment = IVLCmd::assign(&Name { span: variant_expr.span, ident: variant_name.clone() }, variant_expr);
            result = result.seq(&variant_assignment);
            &Expr::new_typed(ExprKind::Infix(Box::new(variant_expr.clone()), Op::Lt, Box::new(Expr::ident(&variant_name, &Type::Int))), Type::Bool)
        },
        _ => &Expr::new_typed(ExprKind::Bool(true), Type::Bool)
    };

    let mut new_cases =  vec![];
    for case in cases.cases.clone() {
        let mut local_variant_assertion = variant_assertion.clone();
        local_variant_assertion.span = case.condition.span.clone();
        let mut loop_invariants_assertions_commands = Cmd::nop();
        for (loop_invariant, loop_invariant_assertion) in &loop_invariants_assertions {
            let mut local_loop_invariant_assertion = loop_invariant_assertion.clone();
            local_loop_invariant_assertion.span = loop_invariant.span.clone();
            loop_invariants_assertions_commands = loop_invariants_assertions_commands.seq(&Cmd::assert(
                &local_loop_invariant_assertion,
                &format!("Loop invariant {} might not be preserved in case {}", loop_invariant.to_string(), case.condition.to_string())
            ));
        }
        new_cases.push(Case {
            condition: case.condition.clone(),
            cmd:
                case.cmd
                .seq(&loop_invariants_assertions_commands)
                .seq(&Cmd::assert(&local_variant_assertion, &format!("Loop variant might not be decreased in case {}", case.condition.clone().to_string())))
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
    let mut case_condition_prefix = IVLCmd::nop();
    for case in cases.clone().cases {
        let assume_case = case_condition_prefix.seq(&IVLCmd::assume(&case.condition));
        case_condition_prefix = case_condition_prefix.seq(&IVLCmd::assume(&case.condition.clone().prefix(PrefixOp::Not)));
        let break_paths = find_break_paths(&case.cmd, assume_case, method_context, loop_context)?;
        for break_path in break_paths {
            //eprintln!("break_path {:#?}", break_path);
            body_translation = body_translation.nondet(&break_path)
        }

    }


    result = result.seq(&body_translation);

    return Ok(result);
}

fn find_break_paths(command: &Cmd, context: IVLCmd, method_context: &MethodContext, loop_context: &LoopContext) -> Result<Vec<IVLCmd>, Error> {
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

fn find_modified_variables(cmd: &Cmd) -> Result<Vec<(Name, Type)>, Error> {
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

fn method_call_to_ivl(result_name: &Option<Name>, args: &Vec<Expr>, span: &Span, method: &MethodRef, fun_name: &Name, method_context: &MethodContext) -> Result<IVLCmd, Error> {
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
        updated_variant_assertion.span = span.clone();
        result = result.seq(&IVLCmd::assert(&updated_variant_assertion, "Method variant might not be decreased"));
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
        updated_pre_cond.span = span.clone();
        result = result.seq(&IVLCmd::assert(
            &updated_pre_cond,
            &format!("Requires {} might not hold", method_pre_condition.to_string())
        ));
    }


    // havoc result variable if exists
    if let Some((return_name, _span, ty)) = return_value {
        result = result.seq(&havoc_to_ivl(return_name, ty))
    }

    // Havoc modified globals variables
    for (modified_global_variable, ty) in method.get().unwrap().modifies() {
        result = result.seq(&havoc_to_ivl(modified_global_variable, ty));
    }

    // assume post-conditions of the method
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

fn insert_division_by_zero_assertions(expr: &Expr, span: &Span) -> Result<IVLCmd, Error> {
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

fn extract_division_assertions(expr: &Expr) -> Result<Vec<Expr>, Error> {
    Ok(match &expr.kind {
        ExprKind::Prefix(_op, e) => extract_division_assertions(e)?,
        ExprKind::Infix(e1, op, e2) if op.clone() == Op::Div || op.clone() == Op::Mod => {
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

fn match_to_ivl(body: &Cases, method_context: &MethodContext, loop_context: &LoopContext) -> Result<IVLCmd, Error> {
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

fn wp_set(ivl: &IVLCmd, post_conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>, Error> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => wp_set_assert(condition, message, post_conditions),
        IVLCmdKind::Assume { condition } => wp_set_assume(condition, post_conditions),
        IVLCmdKind::Seq(cmd1, cmd2) => wp_set_seq(cmd1, cmd2, post_conditions),
        IVLCmdKind::NonDet(cmd1, cmd2) => wp_set_nondet(cmd1, cmd2, post_conditions),
        _ => todo!("Expected Assert, Assume, Seq, or NonDet!"),
    }
}

fn wp_set_nondet(cmd1: &Box<IVLCmd>, cmd2: &Box<IVLCmd>, post_condition: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>, Error> {
    let wp_set1 = wp_set(cmd1, post_condition.clone())?;
    let wp_set2 = wp_set(cmd2, post_condition.clone())?;
    return Ok([wp_set1, wp_set2].concat());
}

fn wp_set_assert(condition: &Expr, message: &String, post_conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>, Error> {
    // for error localization we consider "assert H;" to be equivalent to "assert H; assume H;"
    return Ok([wp_set_assume(condition, post_conditions)?, vec![WeakestPrecondition { expr: condition.clone(), span: condition.span, msg: message.clone() }]].concat());
}

fn wp_set_assume(condition: &Expr, post_conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>, Error> {
    let mut new_conditions: Vec<WeakestPrecondition> = vec![];
    for WeakestPrecondition { expr, span, msg } in post_conditions {
        let new_condition = Expr::new_typed(ExprKind::Infix(Box::new(condition.clone()), Op::Imp, Box::new(expr.clone())), Type::Bool);
        new_conditions.push(WeakestPrecondition { expr: new_condition, span: span, msg: msg });
    }
    return Ok(new_conditions);
}

fn wp_set_seq(cmd1: &Box<IVLCmd>, cmd2: &Box<IVLCmd>, post_condition: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>, Error> {
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
            if (variables.into_iter().map(|x| x.to_string()).collect::<String>()).contains(&identifier.ident.0) {
                return original_expression.clone();
            }
            return replace_in_expression(expr, identifier, replace_with_identifier)
        },
        ExprKind::FunctionCall { fun_name, args, function } => {
            let mut replaced_args = Vec::new();
            for arg in args {
                replaced_args.push(replace_in_expression(arg, identifier, replace_with_identifier));
            }
            Expr::call(fun_name.clone(), replaced_args, function.clone())
        }
        ExprKind::Ite(c, e1, e2) => {
            replace_in_expression(c, identifier, replace_with_identifier).ite(
                &replace_in_expression(e1, identifier, replace_with_identifier),
                &replace_in_expression(e2, identifier, replace_with_identifier)
            )
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
        ExprKind::FunctionCall { fun_name, args, function } => {
            let mut replaced_args = Vec::new();
            for arg in args {
                replaced_args.push(replace_result_in_expression(arg, replace_expression));
            }
            Expr::call(fun_name.clone(), replaced_args, function.clone())
        }
        ExprKind::Ite(c, e1, e2) => {
            replace_result_in_expression(c, replace_expression).ite(
                &replace_result_in_expression(e1, replace_expression),
                &replace_result_in_expression(e2, replace_expression)
            )
        }
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
        ExprKind::FunctionCall { fun_name, args, function } => {
            let mut replaced_args = Vec::new();
            for arg in args {
                replaced_args.push(replace_old_in_expression(arg, global_variables_old_values));
            }
            Expr::call(fun_name.clone(), replaced_args, function.clone())
        }
        ExprKind::Ite(c, e1, e2) => {
            replace_old_in_expression(c, global_variables_old_values).ite(
                &replace_old_in_expression(e1, global_variables_old_values),
                &replace_old_in_expression(e2, global_variables_old_values)
            )
        }
        _ => original_expression.clone(),
    };
    result.span = original_expression.span;
    result
}