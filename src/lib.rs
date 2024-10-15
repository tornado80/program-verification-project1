pub mod ivl;
mod ivl_ext;

use std::vec;

use ivl::{IVLCmd, IVLCmdKind, WeakestPrecondition};
use slang::ast::{Cmd, CmdKind, Expr, ExprKind, Ident, MethodRef, Name, Op, Type};
use slang_ui::prelude::*;
use slang_ui::prelude::slang::ast::{Cases, PrefixOp};
use slang_ui::prelude::slang::Span;

pub struct App;

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &mut slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // Get reference to Z3 solver
        let mut solver = cx.solver()?;

        // Iterate methods
        for m in file.methods() {
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
            // However, we check for satifiability of !(precondition -> wp_predicate)
            // which is equivalent to !(!precondition or wp_predicate) == precondition and !wp_predicate
            // Therefore we assert the precondition and later on assert the negation of each of the wp_predicate's
            solver.assert(spre.as_bool()?)?;


            let post_conditions = m.ensures().map(|e| e.clone()).collect();

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;

            let mut havoc_counter = 0;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd, &mut havoc_counter, &post_conditions)?;

            // Calculate obligation and error message (if obligation is not
            // verified)
            let wp_list = wp_set(&ivl, vec![])?;
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

// Encoding of (assert-only) statements into IVL (for programs comprised of only
// a single assertion)
fn cmd_to_ivlcmd(cmd: &Cmd, havoc_counter: &mut i32, post_conditions: &Vec<Expr>) -> Result<IVLCmd> {
    let &Cmd { kind, span, .. } = &cmd;
    Ok(match kind {
        CmdKind::Assert { condition, message } =>
            insert_division_by_zero_assertions(condition, span)?.seq(&IVLCmd::assert(condition, message)),
        CmdKind::Assume { condition} =>
            insert_division_by_zero_assertions(condition, span)?.seq(&IVLCmd::assume(condition)),
        CmdKind::Seq(cmd1, cmd2) =>
            cmd_to_ivlcmd(cmd1, havoc_counter, &post_conditions)?.seq(&cmd_to_ivlcmd(cmd2, havoc_counter, &post_conditions)?),
        CmdKind::VarDefinition { name, ty:(_, typ) , expr:None  } =>
            havoc_to_ivl(name, typ, havoc_counter),
        CmdKind::VarDefinition { name, ty:_, expr:Some(value)  } =>
            insert_division_by_zero_assertions(value, span)?.seq(&IVLCmd::assign(name, value)),
        CmdKind::Assignment { name, expr } =>
            insert_division_by_zero_assertions(expr, span)?.seq(&IVLCmd::assign(name, expr)),
        CmdKind::Match {body} =>
            match_to_ivl(body, havoc_counter, post_conditions)?,
        CmdKind::Return { expr: Some(value) } =>
            insert_division_by_zero_assertions(value, span)?.seq(
                &IVLCmd::ret_with_expr(value, post_conditions, span)
            ),
        CmdKind::Return { expr: None } => IVLCmd::ret(post_conditions, span),
        CmdKind::MethodCall { name, fun_name, args, method } =>
            method_call_to_ivl(name, fun_name, args, method)?,
        _ => todo!("{:#?}", cmd.kind),
    })
}

fn method_call_to_ivl(name: &Option<Name>, fun_name: &Name, args: &Vec<Expr>, method: &MethodRef) -> Result<IVLCmd> {
    // zero divisions assertions
    let mut result = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    for arg in args {
        result = result.seq(&insert_division_by_zero_assertions(arg, &arg.span.clone())?);
    }
    let arc = method.get().unwrap();
    let requires = arc.requires();
    let ensures = arc.ensures();

    return Ok(result)
}

fn insert_division_by_zero_assertions(expr: &Expr, span: &Span) -> Result<IVLCmd> {
    let divisors = extract_divisors(expr)?;
    let mut assertion = IVLCmd::assert(&Expr::new_typed(ExprKind::Bool(true), Type::Bool), "Please don't fail!");
    if divisors.is_empty() {
        return Ok(assertion.clone());
    }
    for divisor in divisors {
        assertion = assertion.seq(&IVLCmd::assert_with_span(
            &Expr::new_typed(ExprKind::Infix(
                Box::new(divisor),
                Op::Ne,
                Box::new(Expr::new_typed(ExprKind::Num(0), Type::Int))
            ), Type::Bool),
            "Possible division by zero!",
            &span)
        );
    }
    return Ok(assertion);
}

fn extract_divisors(expr: &Expr) -> Result<Vec<Expr>> {
    Ok(match &expr.kind {
        ExprKind::Prefix(_op, e) => extract_divisors(e)?,
        ExprKind::Infix(e1, op, e2) if op.clone() == Op::Div => {
            let mut result = extract_divisors(e1)?.clone();
            result.extend(extract_divisors(e2)?);
            result.extend(vec![*e2.clone()]);
            result
        }
        ExprKind::Infix(e1, _op, e2) => {
            let mut result = extract_divisors(e1)?.clone();
            result.extend(extract_divisors(e2)?);
            result
        }
        ExprKind::Ite(condition, e1, e2) => {
            let mut result = extract_divisors(condition)?.clone();
            result.extend(extract_divisors(e1)?);
            result.extend(extract_divisors(e2)?);
            result
        }
        ExprKind::Quantifier(_q, _v, _b) => vec![], // we are not sure
        ExprKind::FunctionCall { fun_name:_, args, function:_} => {
            let mut args_divisors = vec![];
            for arg in args {
                args_divisors.extend(extract_divisors(arg)?);
            }
            args_divisors
        },
        _ => vec![]
    })
}

fn match_to_ivl(body: &Cases, havoc_counter: &mut i32, post_conditions: &Vec<Expr>) -> Result<IVLCmd> {
    let first_case = body.cases[0].clone();
    let cmd_b: IVLCmd =
        insert_division_by_zero_assertions(&first_case.condition, &first_case.condition.span)?.seq(
            &IVLCmd::assume(&first_case.condition).seq(
                &cmd_to_ivlcmd(&first_case.cmd, havoc_counter, &post_conditions)?
            )
        );
    if body.cases.len() == 1 {
        return Ok(cmd_b);
    }
    let new_body = Cases{ span: body.span, cases: body.cases[1 .. body.cases.len()].to_vec() };
    let cmd_not_b: IVLCmd = IVLCmd::assume(
        &Expr::new_typed(ExprKind::Prefix(PrefixOp::Not,Box::new(first_case.condition.clone())), Type::Bool))
            .seq(&match_to_ivl(&new_body, havoc_counter, post_conditions)?);
    return Ok(cmd_b.nondet(&cmd_not_b));
}

fn havoc_to_ivl(name: &Name, typ: &Type, havoc_counter: &mut i32) -> IVLCmd {
    *havoc_counter += 1;
    return IVLCmd::assign(name, &Expr::new_typed(ExprKind::Ident(Ident(format!("havoc{0}", havoc_counter).to_string())), typ.clone()))
}

fn wp_set(ivl: &IVLCmd, post_conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => wp_set_assert(condition, message, post_conditions),
        IVLCmdKind::Assume { condition } => wp_set_assume(condition, post_conditions),
        IVLCmdKind::Seq(cmd1, cmd2) => wp_set_seq(cmd1, cmd2, post_conditions),
        IVLCmdKind::Assignment { name, expr } => wp_set_assignment(name, expr, post_conditions),
        IVLCmdKind::NonDet(cmd1, cmd2) => wp_set_nondet(cmd1, cmd2, post_conditions),
        IVLCmdKind::Return {expr, method_post_conditions} =>
            wp_set_return(expr, method_post_conditions),

        _ => todo!("Not supported in wp (yet)."),
    }
}

fn wp_set_return(expr: &Option<Expr>, method_post_conditions: &Vec<Expr>) -> Result<Vec<WeakestPrecondition>> {
    // we model the return with the following:
    // return expr
    // assert method_post_conditions[result <- expr]
    // assume false (we just ignore post_conditions and consider )

    // We want to mark ensures as errors if they do not comply with a return
    let mut pre_conditions = vec![];
    for method_post_condition in method_post_conditions {
        let contains_result = check_for_result_in_expression(&method_post_condition);
        if !contains_result {
            continue;
        }

        let replaced = match expr {
            Some(e) => &replace_result_in_expression(&method_post_condition, e),
            None => &method_post_condition
        };
        let found_conditions = wp_set_assert(
            replaced,
            &String::from("Ensure might not hold"),
            vec![]
        )?;
        for mut condition in found_conditions {
            condition.span = method_post_condition.span;
            pre_conditions.push(condition.clone());
        }
    }
    Ok(pre_conditions)
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

fn wp_set_assignment(identifier: &Name, identifier_value: &Expr, conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    let mut updated_conditions: Vec<WeakestPrecondition> = vec![];
    for WeakestPrecondition { expr, span, msg } in conditions {
        let new_condition = replace_in_expression(&expr, identifier, identifier_value);
        updated_conditions.push(WeakestPrecondition { expr: new_condition, span: span, msg: msg });
    }
    return Ok(updated_conditions);
}
// f (e, i, v) -> e[i <- v]
fn replace_in_expression(origin_expression: &Expr, identifier: &Name, identifier_value: &Expr) -> Expr {
    match &origin_expression.kind {
        ExprKind::Ident(name) if name.0 == identifier.ident.0 => identifier_value.clone(),
        ExprKind::Prefix(op, expr) => Expr::new_typed(
            ExprKind::Prefix(
                *op, 
                Box::new(replace_in_expression(expr, identifier, identifier_value))
            ), 
            origin_expression.ty.clone()),
        ExprKind::Infix(lhs, op, rhs) => Expr::new_typed(
            ExprKind::Infix(
                Box::new(replace_in_expression(lhs, identifier, identifier_value)), 
                *op, 
                Box::new(replace_in_expression(rhs, identifier, identifier_value))
            ), 
            origin_expression.ty.clone()),
        _ => origin_expression.clone(),
    }
}

fn check_for_result_in_expression(origin_expression: &Expr) -> bool {
    match &origin_expression.kind {
        ExprKind::Result => true,
        ExprKind::Prefix(_op, expr) => 
            check_for_result_in_expression(&expr),
        ExprKind::Infix(lhs, _op, rhs) => 
            check_for_result_in_expression(&lhs) 
            || check_for_result_in_expression(rhs),
        _ => false,
    }
}

fn replace_result_in_expression(origin_expression: &Expr, replace_expression: &Expr) -> Expr {
    match &origin_expression.kind {
        ExprKind::Result => replace_expression.clone(),
        ExprKind::Prefix(op, expr) => Expr::new_typed(
            ExprKind::Prefix(
                *op,
                Box::new(replace_result_in_expression(expr, replace_expression))
            ),
            origin_expression.ty.clone()),
        ExprKind::Infix(lhs, op, rhs) => Expr::new_typed(
            ExprKind::Infix(
                Box::new(replace_result_in_expression(lhs, replace_expression)),
                *op,
                Box::new(replace_result_in_expression(rhs, replace_expression))
            ),
            origin_expression.ty.clone()),
        _ => origin_expression.clone(),
    }
}