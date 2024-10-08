pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind, WeakestPrecondition};
use slang::ast::{Cmd, CmdKind, Expr, ExprKind, Name};
use slang_ui::prelude::*;

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
            solver.assert(spre.as_bool()?)?;

            // Get method's body
            let cmd = &m.body.clone().unwrap().cmd;
            // Encode it in IVL
            let ivl = cmd_to_ivlcmd(cmd)?;
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
fn cmd_to_ivlcmd(cmd: &Cmd) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Assert { condition, .. } => Ok(IVLCmd::assert(condition, "Assert might fail!")),
        CmdKind::Seq(cmd1, cmd2) => Ok(cmd_to_ivlcmd(cmd1)?.seq(&cmd_to_ivlcmd(cmd2)?)),
        CmdKind::VarDefinition { name, ty:(_, typ) , expr:None  } => Ok(IVLCmd::havoc(name, typ)),
        CmdKind::VarDefinition { name, ty:_, expr:Some(value)  } => Ok(IVLCmd::assign(name, value)),
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),
        _ => todo!("{:#?}", cmd.kind),
    }
}

fn wp_set(ivl: &IVLCmd, conditions: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => Ok([conditions, vec![WeakestPrecondition { expr: condition.clone(), span: condition.span, msg: message.clone() }]].concat()),
        IVLCmdKind::Seq(cmd1, cmd2) => wp_set_seq(cmd1, cmd2, conditions),
        IVLCmdKind::Assignment { name, expr } => Ok(wp_set_assignment(name, expr, conditions)),
        _ => todo!("Not supported in wp (yet)."),
    }
}

fn wp_set_seq(cmd1: &Box<IVLCmd>, cmd2: &Box<IVLCmd>, post_condition: Vec<WeakestPrecondition>) -> Result<Vec<WeakestPrecondition>> {
    let wp_set2 = wp_set(cmd2, post_condition)?;
    let wp_set1 = wp_set(&cmd1, wp_set2)?;
    return Ok(wp_set1);
}

fn wp_set_assignment(identifier: &Name, indentifier_value: &Expr, conditions: Vec<WeakestPrecondition>) -> Vec<WeakestPrecondition> {
    let mut updated_conditions: Vec<WeakestPrecondition> = vec![];
    for WeakestPrecondition { expr, span, msg } in conditions {
        let new_condition = replace_in_expression(&expr, identifier, indentifier_value);
        updated_conditions.push(WeakestPrecondition { expr: new_condition, span: span, msg: msg });
    }

    return updated_conditions;
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