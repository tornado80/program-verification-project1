use slang::{
    ast::{Expr, Name, Type},
    Span,
};
use slang_ui::prelude::*;

#[derive(Debug, Clone)]
pub struct IVLCmd {
    pub span: Span,
    pub kind: IVLCmdKind,
}

#[derive(Debug, Clone)]
pub enum IVLCmdKind {
    Assignment { name: Name, expr: Expr },
    Havoc { name: Name, ty: Type },

    Assume { condition: Expr },
    Assert { condition: Expr, message: String },

    Seq(Box<IVLCmd>, Box<IVLCmd>),
    NonDet(Box<IVLCmd>, Box<IVLCmd>),
    Return { expr: Option<Expr>, method_post_conditions: Vec<WeakestPrecondition> },
}

#[derive(Debug, Clone)]
pub struct WeakestPrecondition {
    pub expr: Expr,
    pub span: Span,
    pub msg: String,
}
