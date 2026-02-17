module

public import Lean
public import ProgramAnalysis.ControlFlowAnalysis.Fun

public section
namespace ProgramAnalysis.ControlFlowAnalysis.Fun.Meta

open Lean Elab Meta ProgramAnalysis.ControlFlowAnalysis.Fun

declare_syntax_cat fun_op
syntax "+" : fun_op
syntax "-" : fun_op
syntax "*" : fun_op
syntax "/" : fun_op
syntax "==" : fun_op
syntax "<" : fun_op
syntax "<=" : fun_op
syntax ">" : fun_op
syntax ">=" : fun_op
syntax "!=" : fun_op

declare_syntax_cat fun_term
syntax num : fun_term
syntax "-" num : fun_term
syntax ident : fun_term
syntax "fn" ident "=>" fun_term : fun_term
syntax fun_term fun_term : fun_term
syntax "if" fun_term "then" fun_term "else" fun_term : fun_term
syntax fun_term fun_op fun_term : fun_term
syntax "let" ident "=" fun_term "in" fun_term : fun_term
syntax "(" fun_term ")" : fun_term

meta def elabOp : Syntax → MetaM Lean.Expr
  | `(fun_op| +) => return .const ``Op.plus []
  | `(fun_op| -) => return .const ``Op.minus []
  | `(fun_op| *) => return .const ``Op.times []
  | `(fun_op| /) => return .const ``Op.div []
  | `(fun_op| ==) => return .const ``Op.eq []
  | `(fun_op| <) => return .const ``Op.lt []
  | `(fun_op| <=) => return .const ``Op.le []
  | `(fun_op| >) => return .const ``Op.gt []
  | `(fun_op| >=) => return .const ``Op.ge []
  | `(fun_op| !=) => return .const ``Op.neq []
  | _ => throwUnsupportedSyntax

meta partial def elabTerm : Syntax → MetaM Lean.Expr
  | `(fun_term| $n:num) => mkAppM ``Expr.mkConst #[mkIntLit n.getNat]
  | `(fun_term| -$n:num) => mkAppM ``Expr.mkConst #[mkIntLit (n.getNat * -1)]
  | `(fun_term| $x:ident) => mkAppM ``Expr.mkVar #[mkStrLit x.getId.toString]
  | `(fun_term| fn $x:ident => $e:fun_term) => do
    let eExpr ← elabTerm e
    mkAppM ``Expr.mkFn #[mkStrLit x.getId.toString, eExpr]
  | `(fun_term| $e1:fun_term $e2:fun_term) => do
    let e1Expr ← elabTerm e1
    let e2Expr ← elabTerm e2
    mkAppM ``Expr.mkApp #[e1Expr, e2Expr]
  | `(fun_term| if $e1:fun_term then $e2:fun_term else $e3:fun_term) => do
    let e1Expr ← elabTerm e1
    let e2Expr ← elabTerm e2
    let e3Expr ← elabTerm e3
    mkAppM ``Expr.mkIte #[e1Expr, e2Expr, e3Expr]
  | `(fun_term| $e1:fun_term $op:fun_op $e2:fun_term) => do
    let e1Expr ← elabTerm e1
    let opExpr ← elabOp op
    let e2Expr ← elabTerm e2
    mkAppM ``Expr.mkOp #[opExpr, e1Expr, e2Expr]
  | `(fun_term| let $x:ident = $e1:fun_term in $e2:fun_term) => do
    let e1Expr ← elabTerm e1
    let e2Expr ← elabTerm e2
    mkAppM ``Expr.mkLetIn #[mkStrLit x.getId.toString, e1Expr, e2Expr]
  | `(fun_term| ($e:fun_term)) => elabTerm e
  | _ => throwUnsupportedSyntax

elab "[Fun|" p:fun_term "]" : term => do
  let pExpr ← elabTerm p
  let pExpr ← mkAppM ``Expr.build #[pExpr]
  return pExpr

#reduce [Fun|(fn x => x)(fn y => y)]

end ProgramAnalysis.ControlFlowAnalysis.Fun.Meta
end
