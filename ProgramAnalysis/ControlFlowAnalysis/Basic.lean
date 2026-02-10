module

public import Std.Data.TreeSet
public import Std.Data.TreeMap

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

def Std.TreeSet.subset (s1 s2 : Std.TreeSet α cmp) : Bool :=
  s1.all s2.contains

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

public inductive ConcreteDomain
  | cache : Label → ConcreteDomain
  | env : Var → ConcreteDomain
deriving Repr, Ord, Inhabited

public def ConcreteDomain.pp : ConcreteDomain → String
  | .cache n => s!"C({n})"
  | .env var => s!"r({var})"

/-- A term value that appears in constraints (always of the form `fn x => e`) -/
public structure FnTerm where
  var : Var
  body : Expr
deriving Repr, Ord

public def FnTerm.pp (t : FnTerm) : String :=
  s!"fn {t.var} => {t.body.pp}"

/--
Constraint is in the form of
- lhs ⊆ rhs
- {t} ⊆ rhs' => lhs ⊆ rhs

rhs is of the form C(l) or r(x)
lhs is of the form C(l), r(x), or {t}
t is of the form fn x => e
-/
public inductive Constraint
  /-- `lhs ⊆ rhs` -/
  | subset (lhs rhs : ConcreteDomain) : Constraint
  /-- `{t} ⊆ rhs` -/
  | literal (t : FnTerm) (rhs : ConcreteDomain) : Constraint
  /-- `{t} ⊆ rhs' → lhs ⊆ rhs` -/
  | conditional (t : FnTerm) (rhs' : ConcreteDomain) (lhs rhs : ConcreteDomain) : Constraint
deriving Repr, Ord

public def Constraint.pp : Constraint → String
  | .subset lhs rhs => s!"{lhs.pp} ⊆ {rhs.pp}"
  | .literal t rhs => s!"{t.pp} ⊆ {rhs.pp}"
  | .conditional t rhs' lhs rhs => s!"{t.pp} ⊆ {rhs'.pp} => {lhs.pp} ⊆ {rhs.pp}"

public def Expr.allFns : Expr → List FnTerm
| .e term _ => match term with
  | .c _ => []
  | .x _ => []
  | .fn x body => [FnTerm.mk x body] ++ allFns body
  | .app t1 t2 => allFns t1 ++ allFns t2
  | .ite t0 t1 t2 => allFns t0 ++ allFns t1 ++ allFns t2
  | .op _ t1 t2 => allFns t1 ++ allFns t2
  | .letin _ t1 t2 => allFns t1 ++ allFns t2

public def Expr.constraints : Expr → ReaderM (List FnTerm) (Std.TreeSet Constraint)
  | .e term label => match term with
    | .c _ => pure ∅
    | .x x => pure {(.subset (.env x) (.cache label))}
    | .ite t0 t1 t2 => do
      let c0 ← constraints t0
      let c1 ← constraints t1
      let c2 ← constraints t2
      return c0 ∪ c1 ∪ c2 ∪
        {(.subset (.cache t1.label) (.cache label))} ∪
        {(.subset (.cache t2.label) (.cache label))}
    | .letin x t1 t2 => do
      let c1 ← constraints t1
      let c2 ← constraints t2
      return c1 ∪ c2 ∪
        {(.subset (.cache t1.label) (.env x))} ∪
        {(.subset (.cache t2.label) (.cache label))}
    | .op _ t1 t2 => do
      let c1 ← constraints t1
      let c2 ← constraints t2
      return c1 ∪ c2
    | .fn x expr => do
      let ce ← constraints expr
      return {Constraint.literal (FnTerm.mk x expr) (.cache label)} ∪ ce
    | .app t1 t2 => do
      let c1 ← constraints t1
      let c2 ← constraints t2
      let fns ← read
      return c1 ∪ c2 ∪
        .ofList (fns.map (fun t => Constraint.conditional t (.cache t1.label) (.cache t2.label) (.env t.var))) ∪
        .ofList (fns.map (fun t => Constraint.conditional t (.cache t1.label) (.cache t.body.label) (.cache label)))

def example2 : Expr := .build <|
  Expr.mkLetIn "f₁" (Expr.mkFn "x₁" (Expr.mkVar "x₁"))
    (Expr.mkLetIn "f₂" (Expr.mkFn "x₂" (Expr.mkVar "x₂"))
    (Expr.mkApp (Expr.mkApp (Expr.mkVar "f₁") (Expr.mkVar "f₂")) (Expr.mkFn "y" (Expr.mkVar "y"))))

#eval example2.pp

def example2Fns := Expr.allFns example2

#eval example2Fns.map (fun t => t.pp)
def example2Constraints := (Expr.constraints example2).run example2Fns

-- #eval example2Constraints.toList.map (fun c => c.pp)

public abbrev Constraint.Node := ConcreteDomain


def Constraint.nodes : Constraint → List Node
  | .subset lhs rhs => [lhs, rhs]
  | .literal _ rhs => [rhs]
  | .conditional _ rhs' lhs rhs => [rhs', lhs, rhs]

def Constraint.solve (constraints: List Constraint) : Std.TreeMap Node (Std.TreeSet FnTerm) := Id.run do
  let nodes : List Node := (constraints.map Constraint.nodes).flatten
  let mut D : Std.TreeMap Node (Std.TreeSet FnTerm) := {}
  let mut E : Std.TreeMap Node (List Constraint) := {}
  let mut W : List Node := []

  let add
    (D : Std.TreeMap Node (Std.TreeSet FnTerm))
    (W : List Node)
    (q : Node)
    (d: Std.TreeSet FnTerm) :
    Std.TreeMap Node (Std.TreeSet FnTerm) × List Node :=
    if !(d.subset D[q]!) then
      ⟨D.insert q (d ∪ D[q]!), q :: W⟩
    else
      ⟨D, W⟩

  -- Step 1: Initialization
  for q in nodes do
    D := D.insert q ∅
    E := E.insert q ∅

  -- Step 2: Building the graph
  for cc in constraints do
    match cc with
    | .literal t p => do
      -- add(p, {t})
      let (D', W') := add D W p {t}; D := D'; W := W'
    | .subset p₁ p₂ => do
      E := E.insert p₁ (cc :: E[p₁]!)
    | .conditional t p p₁ p₂ => do
      E := E.insert p₁ (cc :: E[p₁]!)
      E := E.insert p (cc :: E[p]!)

  -- Step 3: Iteration
  while !W.isEmpty do
    let q := W.head!
    W := W.tail
    for cc in E[q]! do
      match cc with
      | .subset p₁ p₂ => do
        -- add(p₂, D[p₁])
        let (D', W') := add D W p₂ D[p₁]!; D := D'; W := W'
      | .conditional t p p₁ p₂ =>
        if D[p]!.contains t then
          -- add(p₂, D[p₁])
          let (D', W') := add D W p₂ D[p₁]!; D := D'; W := W'
      | _ => continue

  -- Step 4: Recording the solution
  pure D

def example3 : Expr := .build <|
  open Expr in
  mkApp (mkFn "x" (mkVar "x")) (mkFn "y" (mkVar "y"))

def example3.allFns := Expr.allFns example3

def example3.constraints := (Expr.constraints example3).run example3.allFns

#eval example3.constraints.toList.map (fun c => c.pp)

def example3.solution := Constraint.solve example3.constraints.toList

#eval example3.solution.toList.map (fun (node, value) => s!"{node.pp} ↦ {value.toList.map (fun t: FnTerm => t.pp)}")

end ControlFlowAnalysis
