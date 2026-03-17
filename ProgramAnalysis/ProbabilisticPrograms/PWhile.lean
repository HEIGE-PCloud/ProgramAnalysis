module
public import Lean

namespace ProgramAnalysis.ProbabilisticPrograms

public abbrev Var := String

public abbrev Label := Nat

public inductive Op_a
  | plus
  | minus
  | times
  | div
deriving Repr, Ord, DecidableEq

public def Op_a.toString : Op_a → String
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .div => "/"

public instance : ToString Op_a := ⟨Op_a.toString⟩

public inductive Op_b
  | and
  | or
deriving Repr, Ord, DecidableEq

public def Op_b.toString : Op_b → String
  | .and => "∧"
  | .or => "∨"

public instance : ToString Op_b := ⟨Op_b.toString⟩

public inductive Op_r
  | eq
  | lt
  | gt
  | le
  | ge
  | neq
deriving Repr, Ord, DecidableEq

public def Op_r.toString : Op_r → String
  | .eq => "="
  | .lt => "<"
  | .gt => ">"
  | .le => "≤"
  | .ge => "≥"
  | .neq => "≠"

public instance : ToString Op_r := ⟨Op_r.toString⟩

public inductive ArithAtom
  | var : Var → ArithAtom
  | const : Nat → ArithAtom
  | op : Op_a → ArithAtom → ArithAtom → ArithAtom
deriving Repr, Ord, DecidableEq

public def ArithAtom.toString : ArithAtom → String
  | .var x => x
  | .const n => ToString.toString n
  | .op o a1 a2 => s!"({a1.toString} {o.toString} {a2.toString})"

public instance : ToString ArithAtom where
  toString := ArithAtom.toString

public inductive BoolAtom
  | btrue : BoolAtom
  | bfalse : BoolAtom
  | not : BoolAtom → BoolAtom
  | op : Op_b → BoolAtom → BoolAtom → BoolAtom
  | rel : Op_r → ArithAtom → ArithAtom → BoolAtom
deriving Repr, Ord, DecidableEq

public def BoolAtom.toString : BoolAtom → String
  | .btrue => "true"
  | .bfalse => "false"
  | .not b => s!"(¬{b.toString})"
  | .op o b1 b2 => s!"({b1.toString} {o.toString} {b2.toString})"
  | .rel o a1 a2 => s!"({a1.toString} {o.toString} {a2.toString})"

public instance : ToString BoolAtom := ⟨BoolAtom.toString⟩

public inductive Stmt
  | stop : Label → Stmt
  | skip : Label → Stmt
  | assign : Var → ArithAtom → Label → Stmt
  | assign? : Var → List ArithAtom → Label → Stmt
  | seq : Stmt → Stmt → Stmt
  | choose : Label → Nat → Stmt → Nat → Stmt → Stmt
  | sif : BoolAtom → Label → Stmt → Stmt → Stmt
  | swhile : BoolAtom → Label → Stmt → Stmt
deriving Repr, Ord, DecidableEq

public def Stmt.toString : Stmt → String
  | .stop l => s!"[stop]{l.toSuperscriptString}"
  | .skip l => s!"[skip]{l.toSuperscriptString}"
  | .assign var arith l => s!"[{var} := {arith}]{l.toSuperscriptString}"
  | .assign? var ariths l => s!"[{var} ?= {ariths}]{l.toSuperscriptString}"
  | .seq s1 s2 => s!"{s1.toString}\n{s2.toString}"
  | .choose l p1 s1 p2 s2 => s!"[choose]{l.toSuperscriptString} {p1}:{s1.toString} or {p2}:{s2.toString} ro"
  | .sif b l s1 s2 => s!"if [{b}]{l.toSuperscriptString} then {s1.toString} else {s2.toString} fi"
  | .swhile b l s => s!"while [{b}]{l.toSuperscriptString} do {s.toString} od"

public instance : ToString Stmt := ⟨Stmt.toString⟩

def freshLabel : StateM Label Label := do
  let n ← get
  set (n + 1)
  return n

public def Stmt.mkStop : StateM Label Stmt := do
  return Stmt.stop (← freshLabel)

public def Stmt.mkSkip : StateM Label Stmt := do
  return Stmt.skip (← freshLabel)

public def Stmt.mkAssign (x : Var) (a : ArithAtom) : StateM Label Stmt := do
  return Stmt.assign x a (← freshLabel)

public def Stmt.mkAssign? (x : Var) (as : List ArithAtom) : StateM Label Stmt := do
  return Stmt.assign? x as (← freshLabel)

public def Stmt.mkSeq (s1 s2 : StateM Label Stmt) : StateM Label Stmt := do
  return Stmt.seq (← s1) (← s2)

public def Stmt.mkChoose (p1 : Nat) (s1 : StateM Label Stmt) (p2 : Nat) (s2 : StateM Label Stmt) : StateM Label Stmt := do
  return Stmt.choose (← freshLabel) p1 (← s1) p2 (← s2)

public def Stmt.mkIf (b : BoolAtom) (thn els : StateM Label Stmt) : StateM Label Stmt := do
  return Stmt.sif b (← freshLabel) (← thn) (← els)

public def Stmt.mkWhile (b : BoolAtom) (body : StateM Label Stmt) : StateM Label Stmt := do
  return Stmt.swhile b (← freshLabel) (← body)

public def Stmt.build (m : StateM Label Stmt) : Stmt :=
  (m.run 1).1

open Lean Elab Meta

declare_syntax_cat pwhile_op_a
scoped syntax "+" : pwhile_op_a
scoped syntax "-" : pwhile_op_a
scoped syntax "*" : pwhile_op_a
scoped syntax "/" : pwhile_op_a

declare_syntax_cat pwhile_op_b
scoped syntax "&&" : pwhile_op_b
scoped syntax "||" : pwhile_op_b

declare_syntax_cat pwhile_op_r
scoped syntax "==" : pwhile_op_r
scoped syntax "!=" : pwhile_op_r
scoped syntax "<" : pwhile_op_r
scoped syntax "<=" : pwhile_op_r
scoped syntax ">" : pwhile_op_r
scoped syntax ">=" : pwhile_op_r

declare_syntax_cat pwhile_arith_atom
scoped syntax ident : pwhile_arith_atom
scoped syntax num : pwhile_arith_atom
scoped syntax "-" num : pwhile_arith_atom
scoped syntax pwhile_arith_atom pwhile_op_a pwhile_arith_atom : pwhile_arith_atom
scoped syntax "(" pwhile_arith_atom ")" : pwhile_arith_atom

declare_syntax_cat pwhile_bool_atom
scoped syntax "true" : pwhile_bool_atom
scoped syntax "false" : pwhile_bool_atom
scoped syntax "not" pwhile_bool_atom : pwhile_bool_atom
scoped syntax pwhile_bool_atom pwhile_op_b pwhile_bool_atom : pwhile_bool_atom
scoped syntax pwhile_arith_atom pwhile_op_r pwhile_arith_atom : pwhile_bool_atom
scoped syntax "(" pwhile_bool_atom ")" : pwhile_bool_atom

declare_syntax_cat pwhile_stmt
scoped syntax "stop" : pwhile_stmt
scoped syntax "skip" : pwhile_stmt
scoped syntax ident ":=" pwhile_arith_atom : pwhile_stmt
scoped syntax ident "?=" pwhile_arith_atom : pwhile_stmt
scoped syntax pwhile_stmt ";" pwhile_stmt : pwhile_stmt
scoped syntax "choose" num ":" pwhile_stmt "or" num ":" pwhile_stmt "ro": pwhile_stmt
scoped syntax "if" pwhile_bool_atom "then" pwhile_stmt "else" pwhile_stmt "fi" : pwhile_stmt
scoped syntax "while" pwhile_bool_atom "do" "(" pwhile_stmt ")" "od" : pwhile_stmt
scoped syntax "(" pwhile_stmt ")" : pwhile_stmt

meta def elabOpa : Syntax → MetaM Expr
  | `(pwhile_op_a| +) => return .const ``Op_a.plus []
  | `(pwhile_op_a| -) => return .const ``Op_a.minus []
  | `(pwhile_op_a| *) => return .const ``Op_a.times []
  | `(pwhile_op_a| /) => return .const ``Op_a.div []
  | _ => throwUnsupportedSyntax

meta def elabOpb : Syntax → MetaM Expr
  | `(pwhile_op_b| &&) => return .const ``Op_b.and []
  | `(pwhile_op_b| ||) => return .const ``Op_b.or []
  | _ => throwUnsupportedSyntax

meta def elabOpr : Syntax → MetaM Expr
  | `(pwhile_op_r| ==) => return .const ``Op_r.eq []
  | `(pwhile_op_r| !=) => return .const ``Op_r.neq []
  | `(pwhile_op_r| <) => return .const ``Op_r.lt []
  | `(pwhile_op_r| <=) => return .const ``Op_r.le []
  | `(pwhile_op_r| >) => return .const ``Op_r.gt []
  | `(pwhile_op_r| >=) => return .const ``Op_r.ge []
  | _ => throwUnsupportedSyntax

meta partial def elabArithAtom : Syntax → MetaM Expr
  | `(pwhile_arith_atom| $x:ident) => mkAppM ``ArithAtom.var #[mkStrLit x.getId.toString]
  | `(pwhile_arith_atom| $n:num) => mkAppM ``ArithAtom.const #[mkIntLit n.getNat]
  | `(pwhile_arith_atom| -$n:num) => mkAppM ``ArithAtom.const #[mkIntLit (n.getNat * -1)]
  | `(pwhile_arith_atom| $a:pwhile_arith_atom $op:pwhile_op_a $b:pwhile_arith_atom) => do
    let aExpr ← elabArithAtom a
    let opExpr ← elabOpa op
    let bExpr ← elabArithAtom b
    mkAppM ``ArithAtom.op #[opExpr, aExpr, bExpr]
  | `(pwhile_arith_atom| ($a:pwhile_arith_atom)) => elabArithAtom a
  | _ => throwUnsupportedSyntax

meta partial def elabBoolAtom : Syntax → MetaM Expr
  | `(pwhile_bool_atom| true) => return .const ``BoolAtom.btrue []
  | `(pwhile_bool_atom| false) => return .const ``BoolAtom.bfalse []
  | `(pwhile_bool_atom| not $b:pwhile_bool_atom) => do
    let bExpr ← elabBoolAtom b
    mkAppM ``BoolAtom.not #[bExpr]
  | `(pwhile_bool_atom| $a:pwhile_bool_atom $op:pwhile_op_b $b:pwhile_bool_atom) => do
    let aExpr ← elabBoolAtom a
    let opExpr ← elabOpb op
    let bExpr ← elabBoolAtom b
    mkAppM ``BoolAtom.op #[opExpr, aExpr, bExpr]
  | `(pwhile_bool_atom| $a:pwhile_arith_atom $op:pwhile_op_r $b:pwhile_arith_atom) => do
    let aExpr ← elabArithAtom a
    let opExpr ← elabOpr op
    let bExpr ← elabArithAtom b
    mkAppM ``BoolAtom.rel #[opExpr, aExpr, bExpr]
  | `(pwhile_bool_atom| ($b:pwhile_bool_atom)) => elabBoolAtom b
  | _ => throwUnsupportedSyntax

meta partial def elabStmt : Syntax → MetaM Expr
  | `(pwhile_stmt| stop) => do
    mkAppM ``Stmt.mkSkip #[]
  | `(pwhile_stmt| skip) => do
    mkAppM ``Stmt.mkSkip #[]
  | `(pwhile_stmt| $x:ident := $a:pwhile_arith_atom) => do
    let aExpr ← elabArithAtom a
    mkAppM ``Stmt.mkAssign #[mkStrLit x.getId.toString, aExpr]
  -- | `(pwhile_stmt| $x:ident ?= $a:pwhile_arith_atom) => do
  --   let aExpr ← elabArithAtom a
  --   mkAppM ``Stmt.mkAssign? #[mkStrLit x.getId.toString, aExpr]
  | `(pwhile_stmt| $s1:pwhile_stmt ; $s2:pwhile_stmt) => do
    let s1Expr ← elabStmt s1
    let s2Expr ← elabStmt s2
    mkAppM ``Stmt.mkSeq #[s1Expr, s2Expr]
  | `(pwhile_stmt| if $b:pwhile_bool_atom then $s1:pwhile_stmt else $s2:pwhile_stmt fi) => do
    let bExpr ← elabBoolAtom b
    let s1Expr ← elabStmt s1
    let s2Expr ← elabStmt s2
    mkAppM ``Stmt.mkIf #[bExpr, s1Expr, s2Expr]
  | `(pwhile_stmt| while $b:pwhile_bool_atom do ($s:pwhile_stmt) od) => do
    let bExpr ← elabBoolAtom b
    let sExpr ← elabStmt s
    mkAppM ``Stmt.mkWhile #[bExpr, sExpr]
  | `(pwhile_stmt| ($s:pwhile_stmt)) => elabStmt s
  | _ => throwUnsupportedSyntax

meta def elabPWhile (stx : Syntax) : MetaM Expr := do
  let expr ← elabStmt stx
  let expr ← mkAppM ``Stmt.build #[expr]
  return expr

elab "[pWhile|" p:pwhile_stmt "]" : term => elabPWhile p

end ProgramAnalysis.ProbabilisticPrograms
