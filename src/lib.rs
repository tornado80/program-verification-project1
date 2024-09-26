pub mod ivl;
mod ivl_ext;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, ExprKind, Op, Type};
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
            let (oblig, msg) = wp(&ivl, &Expr::bool(true))?;
            // Convert obligation to SMT expression
            let soblig = oblig.smt()?;

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
                        cx.error(oblig.span, format!("{msg}"));
                    }
                    smtlib::SatResult::Unknown => {
                        cx.warning(oblig.span, "{msg}: unknown sat result");
                    }
                    smtlib::SatResult::Unsat => (),
                }
                Ok(())
            })?;
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
        _ => todo!("{:#?}", cmd.kind),
    }
}

fn wp(ivl: &IVLCmd, post_condition: &Expr) -> Result<(Expr, String)> {
    match &ivl.kind {
        IVLCmdKind::Assert { condition, message } => Ok((Expr::new_typed(ExprKind::Infix(Box::new(condition.clone()), Op::And, Box::new(post_condition.clone())), Type::Bool), message.clone())),
        IVLCmdKind::Seq(cmd1, cmd2) => Ok((wp(cmd1, &wp(cmd2, post_condition)?.0)?.0, String::from("Unkown error: seq"))),
        IVLCmdKind::Havoc { name:_, ty:_ } => Ok((post_condition.clone(), String::from("Unkown error: havoc"))),
        IVLCmdKind::Assignment { name, expr } => Ok((post_condition.clone(), String::from("Unkown error: assignment"))),
        _ => todo!("Not supported in wp (yet)."),
    }
}