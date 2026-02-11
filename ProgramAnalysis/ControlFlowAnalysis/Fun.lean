module
public import ProgramAnalysis.ControlFlowAnalysis.Basic

/-!
# Fun

Fun is a simple ML-like functional language used to demonstrate control flow
analysis.
-/

/-!
## Syntax of Fun

e ∈ Exp expressions (or labelled terms)
t ∈ Term terms (or unlabelled expressions)

e ::= tˡ
t ::= C | x | fn x => e₀ | e₁ e₂ | if e₁ then e₂ else e₃ | e₁ op e₂ | let x = e₁ in e₂
-/

namespace ProgramAnalysis.ControlFlowAnalysis.Fun

public inductive Op
  | plus
  | minus
  | times
  | div
  | eq
  | lt
  | gt
  | le
  | ge
  | neq
deriving Repr, Ord

def Op.pp : Op → String
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .div => "/"
  | .eq => "=="
  | .lt => "<"
  | .gt => ">"
  | .le => "<="
  | .ge => ">="
  | .neq => "!="

def x := Nat.zero

public section -- See: https://github.com/leanprover/lean4/issues/10067
mutual
public inductive Expr
  | e : Term → Label → Expr
deriving Repr, Ord

public inductive Term
  | c : Nat → Term
  | x : Var → Term
  | fn : Var → Expr → Term
  | app : Expr → Expr → Term
  | ite : Expr → Expr → Expr → Term
  | op : Op → Expr → Expr → Term
  | letin : Var → Expr → Expr → Term
deriving Repr, Ord
end
end

public section -- See: https://github.com/leanprover/lean4/issues/10067
mutual
public def Term.pp : Term → String
  | .c n => s!"{n}"
  | .x v => s!"{v}"
  | .fn x body => s!"(fn {x} => {body.pp})"
  | .app e1 e2 => s!"({e1.pp} {e2.pp})"
  | .ite cond thn els => s!"(if {cond.pp} then {thn.pp} else {els.pp})"
  | .op o e1 e2 => s!"({e1.pp} {o.pp} {e2.pp})"
  | .letin x e1 e2 => s!"(let {x} = {e1.pp} in {e2.pp})"

public def Expr.pp : Expr → String
  | .e t l => s!"{t.pp}{l.toSuperscript}"
end
end

example : Expr := Expr.e (
  Term.app
    (Expr.e (Term.fn "x" (Expr.e (Term.x "x") 1)) 2)
    (Expr.e (Term.fn "y" (Expr.e (Term.x "y") 3)) 4)
) 5

public def Expr.label : Expr → Label
  | Expr.e _ n => n

def freshLabel : StateM Label Label := do
  let n ← get
  set (n + 1)
  return n

public def Expr.mkConst (n : Label) : StateM Label Expr := do
  let l ← freshLabel
  return Expr.e (Term.c n) l

public def Expr.mkVar (x : Var) : StateM Label Expr := do
  let l ← freshLabel
  return Expr.e (Term.x x) l

public def Expr.mkFn (x : Var) (body : StateM Label Expr) : StateM Label Expr := do
  let b ← body
  let l ← freshLabel
  return Expr.e (Term.fn x b) l

public def Expr.mkApp (e1 e2 : StateM Label Expr) : StateM Label Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.app a b) l

public def Expr.mkIte (cond thn els : StateM Label Expr) : StateM Label Expr := do
  let c ← cond
  let t ← thn
  let e ← els
  let l ← freshLabel
  return Expr.e (Term.ite c t e) l

public def Expr.mkOp (o : Op) (e1 e2 : StateM Label Expr) : StateM Label Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.op o a b) l

public def Expr.mkLetIn (x : Var) (e1 e2 : StateM Label Expr) : StateM Label Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.letin x a b) l

public def Expr.build (m : StateM Label Expr) : Expr :=
  (m.run 1).1

/--
((fn x => x¹)² (fn y => y³)⁴)⁵
-/
example : Expr := .build <|
  Expr.mkApp (Expr.mkFn "x" (Expr.mkVar "x")) (Expr.mkFn "y" (Expr.mkVar "y"))

end ProgramAnalysis.ControlFlowAnalysis.Fun
