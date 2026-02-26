module

public import Lean
public import ProgramAnalysis.DataFlowAnalysis.While

public section
namespace ProgramAnalysis.ControlFlowAnalysis.While.Meta

open Lean Elab Meta ProgramAnalysis.DataFlowAnalysis.While

declare_syntax_cat while_op_a
syntax "+" : while_op_a
syntax "-" : while_op_a
syntax "*" : while_op_a
syntax "/" : while_op_a

declare_syntax_cat while_op_b
syntax "&&" : while_op_b
syntax "||" : while_op_b

declare_syntax_cat while_op_r
syntax "==" : while_op_r
syntax "!=" : while_op_r
syntax "<" : while_op_r
syntax "<=" : while_op_r
syntax ">" : while_op_r
syntax ">=" : while_op_r

declare_syntax_cat while_arith_atom
syntax ident : while_arith_atom
syntax num : while_arith_atom
syntax "-" num : while_arith_atom
syntax while_arith_atom while_op_a while_arith_atom : while_arith_atom
syntax "(" while_arith_atom ")" : while_arith_atom

declare_syntax_cat while_bool_atom
syntax "true" : while_bool_atom
syntax "false" : while_bool_atom
syntax "not" while_bool_atom : while_bool_atom
syntax while_bool_atom while_op_b while_bool_atom : while_bool_atom
syntax while_arith_atom while_op_r while_arith_atom : while_bool_atom
syntax "(" while_bool_atom ")" : while_bool_atom

declare_syntax_cat while_stmt
syntax ident ":=" while_arith_atom : while_stmt
syntax "skip" : while_stmt
syntax while_stmt ";" while_stmt : while_stmt
syntax "if" while_bool_atom "then" while_stmt "else" while_stmt : while_stmt
syntax "while" while_bool_atom "do" "(" while_stmt ")" : while_stmt
syntax "(" while_stmt ")" : while_stmt

meta def elabOpa : Syntax → MetaM Expr
  | `(while_op_a| +) => return .const ``Op_a.plus []
  | `(while_op_a| -) => return .const ``Op_a.minus []
  | `(while_op_a| *) => return .const ``Op_a.times []
  | `(while_op_a| /) => return .const ``Op_a.div []
  | _ => throwUnsupportedSyntax

meta def elabOpb : Syntax → MetaM Expr
  | `(while_op_b| &&) => return .const ``Op_b.and []
  | `(while_op_b| ||) => return .const ``Op_b.or []
  | _ => throwUnsupportedSyntax

meta def elabOpr : Syntax → MetaM Expr
  | `(while_op_r| ==) => return .const ``Op_r.eq []
  | `(while_op_r| !=) => return .const ``Op_r.neq []
  | `(while_op_r| <) => return .const ``Op_r.lt []
  | `(while_op_r| <=) => return .const ``Op_r.le []
  | `(while_op_r| >) => return .const ``Op_r.gt []
  | `(while_op_r| >=) => return .const ``Op_r.ge []
  | _ => throwUnsupportedSyntax

meta partial def elabArithAtom : Syntax → MetaM Expr
  | `(while_arith_atom| $x:ident) => mkAppM ``ArithAtom.var #[mkStrLit x.getId.toString]
  | `(while_arith_atom| $n:num) => mkAppM ``ArithAtom.const #[mkIntLit n.getNat]
  | `(while_arith_atom| -$n:num) => mkAppM ``ArithAtom.const #[mkIntLit (n.getNat * -1)]
  | `(while_arith_atom| $a:while_arith_atom $op:while_op_a $b:while_arith_atom) => do
    let aExpr ← elabArithAtom a
    let opExpr ← elabOpa op
    let bExpr ← elabArithAtom b
    mkAppM ``ArithAtom.op #[opExpr, aExpr, bExpr]
  | `(while_arith_atom| ($a:while_arith_atom)) => elabArithAtom a
  | _ => throwUnsupportedSyntax

meta partial def elabBoolAtom : Syntax → MetaM Expr
  | `(while_bool_atom| true) => return .const ``BoolAtom.btrue []
  | `(while_bool_atom| false) => return .const ``BoolAtom.bfalse []
  | `(while_bool_atom| not $b:while_bool_atom) => do
    let bExpr ← elabBoolAtom b
    mkAppM ``BoolAtom.not #[bExpr]
  | `(while_bool_atom| $a:while_bool_atom $op:while_op_b $b:while_bool_atom) => do
    let aExpr ← elabBoolAtom a
    let opExpr ← elabOpb op
    let bExpr ← elabBoolAtom b
    mkAppM ``BoolAtom.op #[opExpr, aExpr, bExpr]
  | `(while_bool_atom| $a:while_arith_atom $op:while_op_r $b:while_arith_atom) => do
    let aExpr ← elabArithAtom a
    let opExpr ← elabOpr op
    let bExpr ← elabArithAtom b
    mkAppM ``BoolAtom.rel #[opExpr, aExpr, bExpr]
  | `(while_bool_atom| ($b:while_bool_atom)) => elabBoolAtom b
  | _ => throwUnsupportedSyntax

meta partial def elabStmt : Syntax → MetaM Expr
  | `(while_stmt| $x:ident := $a:while_arith_atom) => do
    let aExpr ← elabArithAtom a
    mkAppM ``Stmt.mkAssign #[mkStrLit x.getId.toString, aExpr]
  | `(while_stmt| skip) => do
    mkAppM ``Stmt.mkSkip #[]
  | `(while_stmt| $s1:while_stmt ; $s2:while_stmt) => do
    let s1Expr ← elabStmt s1
    let s2Expr ← elabStmt s2
    mkAppM ``Stmt.mkSeq #[s1Expr, s2Expr]
  | `(while_stmt| if $b:while_bool_atom then $s1:while_stmt else $s2:while_stmt) => do
    let bExpr ← elabBoolAtom b
    let s1Expr ← elabStmt s1
    let s2Expr ← elabStmt s2
    mkAppM ``Stmt.mkIf #[bExpr, s1Expr, s2Expr]
  | `(while_stmt| while $b:while_bool_atom do ($s:while_stmt)) => do
    let bExpr ← elabBoolAtom b
    let sExpr ← elabStmt s
    mkAppM ``Stmt.mkWhile #[bExpr, sExpr]
  | `(while_stmt| ($s:while_stmt)) => elabStmt s
  | _ => throwUnsupportedSyntax

meta def elabWhile (stx : Syntax) : MetaM Expr := do
  let expr ← elabStmt stx
  let expr ← mkAppM ``Stmt.build #[expr]
  return expr

elab "[While|" p:while_stmt "]" : term => elabWhile p

#reduce [While|
  y := x;
  z := y;
  while y > 1 do (
    z := z * y;
    y := y - 1
  );
  y := 0
]

end ProgramAnalysis.ControlFlowAnalysis.While.Meta
end
