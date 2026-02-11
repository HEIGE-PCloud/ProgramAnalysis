module
public import ProgramAnalysis.ControlFlowAnalysis.Basic
public import ProgramAnalysis.ControlFlowAnalysis.Fun
public import Std.Data.TreeSet
public import Std.Data.TreeMap

namespace ProgramAnalysis.ControlFlowAnalysis

open ProgramAnalysis.ControlFlowAnalysis.Fun

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

public def Fun.Expr.allFns : Expr → List FnTerm
| .e term _ => match term with
  | .c _ => []
  | .x _ => []
  | .fn x body => [FnTerm.mk x body] ++ allFns body
  | .app t1 t2 => allFns t1 ++ allFns t2
  | .ite t0 t1 t2 => allFns t0 ++ allFns t1 ++ allFns t2
  | .op _ t1 t2 => allFns t1 ++ allFns t2
  | .letin _ t1 t2 => allFns t1 ++ allFns t2

public def Fun.Expr.constraints : Expr → ReaderM (List FnTerm) (Set Constraint)
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

public abbrev Constraint.Node := ConcreteDomain

public def Constraint.nodes : Constraint → List Node
  | .subset lhs rhs => [lhs, rhs]
  | .literal _ rhs => [rhs]
  | .conditional _ rhs' lhs rhs => [rhs', lhs, rhs]

public def Constraint.solve (constraints: List Constraint) : Map Node (Set FnTerm) := Id.run do
  let nodes : List Node := (constraints.map Constraint.nodes).flatten
  let mut D : Map Node (Set FnTerm) := {}
  let mut E : Map Node (List Constraint) := {}
  let mut W : List Node := []

  let add
    (D : Map Node (Set FnTerm))
    (W : List Node)
    (q : Node)
    (d: Set FnTerm) :
    Map Node (Set FnTerm) × List Node :=
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

-- TODO: Control Flow + Data Flow
end ProgramAnalysis.ControlFlowAnalysis
