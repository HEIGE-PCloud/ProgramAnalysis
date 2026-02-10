module

import Std

def Char.toSuperScript : Char → Char
  | '0' => '⁰'
  | '1' => '¹'
  | '2' => '²'
  | '3' => '³'
  | '4' => '⁴'
  | '5' => '⁵'
  | '6' => '⁶'
  | '7' => '⁷'
  | '8' => '⁸'
  | '9' => '⁹'
  | c => c

def Nat.toSuperscript (n : Nat) : String := (toString n).map Char.toSuperScript

namespace ControlFlowAnalysis
public abbrev Label := Nat

public abbrev Var := String

public inductive Op
  | plus
deriving Repr, Ord

def Op.pp : Op → String
  | .plus => "+"

mutual
public inductive Expr
  | e : Term → Label → Expr
deriving Repr, Ord

public inductive Term
  | c : Label → Term
  | x : Var → Term
  | fn : Var → Expr → Term
  | app : Expr → Expr → Term
  | ite : Expr → Expr → Expr → Term
  | op : Op → Expr → Expr → Term
  | letin : Var → Expr → Expr → Term
deriving Repr, Ord
end

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

def example1 : Expr := .build <|
  Expr.mkApp (Expr.mkFn "x" (Expr.mkVar "x")) (Expr.mkFn "y" (Expr.mkVar "y"))

#eval example1

/-- Constraint data type
Constraint is in the form of
lhs ⊆ rhs
{t} ⊆ rhs' => lhs ⊆ rhs
where
rhs is of the form C(l) or r(x)
lhs is of the form C(l), r(x), or {t}
all occurances of t are of the form fn x => e
-/
public inductive AbstractDomain
  | cache : Label → AbstractDomain
  | env : Var → AbstractDomain
deriving Repr

public def AbstractDomain.pp : AbstractDomain → String
  | .cache n => s!"C({n})"
  | .env var => s!"r({var})"

/-- A term value that appears in constraints (always of the form `fn x => e`) -/
public structure FnTerm where
  var : Var
  body : Expr
deriving Repr

public def FnTerm.pp (t : FnTerm) : String :=
  s!"fn {t.var} => {t.body.pp}"

public inductive Constraint
  /-- `lhs ⊆ rhs` -/
  | subset (lhs rhs : AbstractDomain) : Constraint
  /-- `{t} ⊆ rhs` -/
  | literal (t : FnTerm) (rhs : AbstractDomain) : Constraint
  /-- `{t} ⊆ rhs' → lhs ⊆ rhs` -/
  | conditional (t : FnTerm) (rhs' : AbstractDomain) (lhs rhs : AbstractDomain) : Constraint
deriving Repr

public def Constraint.pp : Constraint → String
  | .subset lhs rhs => s!"{lhs.pp} ⊆ {rhs.pp}"
  | .literal t rhs => s!"{t.pp} ⊆ {rhs.pp}"
  | .conditional t rhs' lhs rhs => s!"{t.pp} ⊆ {rhs'.pp} => {lhs.pp} ⊆ {rhs.pp}"

public def allFns : Expr → List FnTerm
| .e term _ => match term with
  | .c _ => []
  | .x _ => []
  | .fn x body => [FnTerm.mk x body] ++ allFns body
  | .app t1 t2 => allFns t1 ++ allFns t2
  | .ite t0 t1 t2 => allFns t0 ++ allFns t1 ++ allFns t2
  | .op _ t1 t2 => allFns t1 ++ allFns t2
  | .letin _ t1 t2 => allFns t1 ++ allFns t2


public def constraints : Expr → ReaderM (List FnTerm) (List Constraint)
  | .e term label => match term with
    | .c _ => pure []
    | .x x => pure [.subset (.env x) (.cache label)]
    | .ite t0 t1 t2 => do
      let c0 ← constraints t0
      let c1 ← constraints t1
      let c2 ← constraints t2
      return c0 ++ c1 ++ c2 ++
        [.subset (.cache t1.label) (.cache label)] ++
        [.subset (.cache t2.label) (.cache label)]
    | .letin x t1 t2 => do
      let c1 ← constraints t1
      let c2 ← constraints t2
      return c1 ++ c2 ++
        [.subset (.cache t1.label) (.env x)] ++
        [.subset (.cache t2.label) (.cache label)]
    | .op _ t1 t2 => do
      let c1 ← constraints t1
      let c2 ← constraints t2
      return c1 ++ c2
    | .fn x e => do
      let ce ← constraints e
      return [Constraint.literal (FnTerm.mk x e) (.cache label)] ++ ce
    | .app t1 t2 => do
      let c1 ← constraints t1
      let c2 ← constraints t2
      let fns ← read
      return c1 ++ c2 ++
        (fns.map (fun t => Constraint.conditional t (.cache t1.label) (.cache t2.label) (.env t.var))) ++
        (fns.map (fun t => Constraint.conditional t (.cache t1.label) (.cache t.body.label) (.cache label)))

def example2 : Expr := .build <|
  Expr.mkLetIn "f₁" (Expr.mkFn "x₁" (Expr.mkVar "x₁"))
    (Expr.mkLetIn "f₂" (Expr.mkFn "x₂" (Expr.mkVar "x₂"))
    (Expr.mkApp (Expr.mkApp (Expr.mkVar "f₁") (Expr.mkVar "f₂")) (Expr.mkFn "y" (Expr.mkVar "y"))))

#eval example2.pp

def example2Fns := allFns example2

#eval example2Fns.map (fun t => t.pp)
def example2Constraints := (constraints example2).run example2Fns

#eval example2Constraints.map (fun c => c.pp)

def solveConstraints (constraints: List Constraint) : Std.TreeMap Var (Std.TreeSet Term) := sorry
end ControlFlowAnalysis
