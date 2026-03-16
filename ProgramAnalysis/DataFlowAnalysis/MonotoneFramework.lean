module
public import Mathlib.Data.Finset.Basic
public import Std.Data.TreeSet
public import ProgramAnalysis.DataFlowAnalysis.While

namespace ProgramAnalysis.DataFlowAnalysis

/-- A partial order on a type `L`, given by a relation `leq` that is
    reflexive, transitive, and antisymmetric. -/
public class PartialOrder (L : Type) where
  leq : L → L → Prop
  refl : ∀ x : L, leq x x
  trans : ∀ x y z : L, leq x y → leq y z → leq x z
  antisymm : ∀ x y : L, leq x y → leq y x → x = y

scoped notation:50 x " ⊑ " y => PartialOrder.leq x y

/-- Integers ordered by the usual ≤ form a partial order. -/
public instance : PartialOrder Int where
  leq i1 i2 := i1 ≤ i2
  refl x := by grind
  trans x y z h1 h2 := by grind
  antisymm x y h1 h2 := by grind


/-- The powerset of a type `X`, ordered by subset inclusion, forms a partial order. -/
public instance {X : Type} : PartialOrder (Finset X) where
  leq A B            := A ⊆ B
  refl A             := Finset.Subset.refl A
  trans _ _ _ h1 h2  := Finset.Subset.trans h1 h2
  antisymm _ _ h1 h2 := Finset.Subset.antisymm h1 h2

section Bounds

variable {L : Type} [PartialOrder L]

/-- `u` is an upper bound of a set `Y` if every element of `Y` is ⊑ u. -/
def UpperBound (Y : Set L) (u : L) : Prop :=
  ∀ y, Y y → y ⊑ u

/-- `l` is a lower bound of a set `Y` if l is ⊑ every element of `Y`. -/
def LowerBound (Y : Set L) (l : L) : Prop :=
  ∀ y, Y y → l ⊑ y

/-- `u` is the least upper bound (join) of `Y` if it is an upper bound and
    is ⊑ every other upper bound. -/
public def LeastUpperBound (Y : Set L) (u : L) : Prop :=
  UpperBound Y u ∧ ∀ u', UpperBound Y u' → u ⊑ u'

/-- `l` is the greatest lower bound (meet) of `Y` if it is a lower bound and
    every other lower bound is ⊑ it. -/
public def GreatestLowestBound (Y : Set L) (l : L) : Prop :=
  LowerBound Y l ∧ ∀ l', LowerBound Y l' → l' ⊑ l

end Bounds

/-- A complete lattice is a partial order where every subset has both a least upper bound
    (`sSup`) and a greatest lower bound (`sInf`). -/
public class CompleteLattice (L : Type) extends PartialOrder L where
  sSup    : Set L → L
  sInf    : Set L → L
  is_lub  : ∀ (Y : Set L), LeastUpperBound Y (sSup Y)
  is_glb  : ∀ (Y : Set L), GreatestLowestBound Y (sInf Y)

scoped notation:65 "⨆ " => CompleteLattice.sSup
scoped notation:65 "⨅ " => CompleteLattice.sInf


----------------------------------------

public structure MonotoneFramework where
  name : String := "Analysis"
  value : Type
  beq : BEq value
  toString : ToString value
  leq : value → value → Bool
  join : value → value → value
  bot : Stmt → value
  extremeValue : Stmt → value
  extremeLabel : Stmt → Std.TreeSet Label
  flow : Stmt → List (Label × Label)
  transfer : Stmt → Label → value → value

public instance (m : MonotoneFramework) : BEq m.value := m.beq

public instance (m : MonotoneFramework) : ToString m.value := m.toString

public inductive Equation.AtomType
  | e0
  | e1
deriving DecidableEq, Repr, Ord

public def Equation.AtomType.toString : Equation.AtomType → String
  | e0 => "◦"
  | e1 => "•"

public instance : ToString Equation.AtomType := ⟨Equation.AtomType.toString⟩

public structure Equation.Atom where
  label : Label
  ty : Equation.AtomType
deriving BEq, DecidableEq, Repr, Ord

public def Equation.Atom.toString (e : Equation.Atom) : String :=
  s!"{e.ty}({e.label})"

public instance : ToString Equation.Atom := ⟨Equation.Atom.toString⟩

public inductive Equation.Expr (value : Type) where
  | bot : Equation.Expr value
  | lit : value → Equation.Expr value
  | atom : Equation.Atom → Equation.Expr value
  | join : Equation.Expr value → Equation.Expr value → Equation.Expr value
  | app : (value → value) → Equation.Atom → Equation.Expr value

public structure Equation (value : Type) : Type where
  lhs : Equation.Atom
  rhs : Equation.Expr value

def MonotoneFramework.eval
  (m : MonotoneFramework)
  (stmt : Stmt)
  (env : Std.TreeMap Equation.Atom m.value)
  : Equation.Expr m.value → m.value
  | .bot => m.bot stmt
  | .lit v => v
  | .atom a => env.getD a (m.bot stmt)
  | .join e1 e2 =>
    let e1' := m.eval stmt env e1
    let e2' := m.eval stmt env e2
    m.join e1' e2'
  | .app f a =>
    let a' := env.getD a (m.bot stmt)
    f a'

public def foldExpr
  (op : Equation.Expr α → Equation.Expr α → Equation.Expr α)
  : List (Equation.Expr α) → Equation.Expr α
  | [] => .bot
  | x :: [] => x
  | x :: xs => op x (foldExpr op xs)

public def MonotoneFramework.e0
  (m : MonotoneFramework) (stmt : Stmt) (l : Label)
  : Equation m.value :=
  let E := m.extremeLabel stmt
  let ι := m.extremeValue stmt
  let F := m.flow stmt
  let lhs := ⟨l, .e0⟩
  let rhs :=
    if l ∈ E then
      .lit ι
    else
      let as : List (Equation.Expr (m.value)) := F.filterMap (fun (l', ll) =>
        if l == ll then
          some (Equation.Expr.atom ⟨l', .e1⟩)
        else
          none)
      foldExpr .join as
  ⟨lhs, rhs⟩

public def MonotoneFramework.e1
  (m : MonotoneFramework) (stmt : Stmt) (l : Label)
  : Equation m.value :=
  let lhs := ⟨l, .e1⟩
  let rhs := .app (m.transfer stmt l) ⟨l, .e0⟩
  ⟨lhs, rhs⟩

public def MonotoneFramework.equations
  (m : MonotoneFramework) (s : Stmt)
  : List (Equation m.value) :=
  s.labels.flatMap (fun l => [m.e0 s l, m.e1 s l])

public def MonotoneFramework.init
  (m : MonotoneFramework) (s : Stmt) (es : List (Equation m.value))
  : Std.TreeMap Equation.Atom m.value :=
  let bot := m.bot s
  es.foldl (fun acc eq => acc.insert eq.lhs bot) ∅


def chaoticIterationOnce
  (m : MonotoneFramework)
  (stmt : Stmt)
  (env : Std.TreeMap Equation.Atom m.value)
  (es : List (Equation m.value))
  : Std.TreeMap Equation.Atom m.value :=
  es.foldl (fun acc eq => acc.insert eq.lhs (m.eval stmt env eq.rhs)) env

-- TODO: Prove termination?
partial def chaoticIteration'
  (m : MonotoneFramework)
  (stmt : Stmt)
  (es : List (Equation m.value))
  (env : Std.TreeMap Equation.Atom m.value) :=
  let env' := chaoticIterationOnce m stmt env es
  if env' == env then env
  else chaoticIteration' m stmt es env'

public def MonotoneFramework.chaoticIteration (m : MonotoneFramework)
  (stmt : Stmt)
  : Std.TreeMap Equation.Atom m.value :=
  let es := m.equations stmt
  chaoticIteration' m stmt es (m.init stmt es)

public def println {m : MonotoneFramework} [ToString m.value]
  (solution : Std.TreeMap Equation.Atom m.value) : IO Unit :=
  solution.toList.forM (fun (k, v) => IO.println s!"{m.name}{k} = {v}")

public def MonotoneFramework.worklistAlgorithm (m : MonotoneFramework) (stmt : Stmt) : Std.TreeMap Equation.Atom m.value := Id.run do
  let F := m.flow stmt
  let E := m.extremeLabel stmt
  let ι := m.extremeValue stmt
  let f := m.transfer stmt
  let bot := m.bot stmt
  let leq := m.leq
  let join := m.join
  let labels := E.insertMany (F.flatMap (fun (a, b) => [a, b]))
  let mut W : List (Label × Label) := []
  let mut Analysis : Std.TreeMap Label m.value := ∅
  let get : Std.TreeMap Label m.value → Label → m.value := fun m l => m.getD l bot

  -- Step 1: Initialization
  for (l, l') in F do
    W := List.cons (l, l') W

  for l in labels do
    if l ∈ E
      then Analysis := Analysis.insert l ι
      else Analysis := Analysis.insert l bot

  -- Step 2: Interation
  while h : W ≠ [] do
    let (l, l')  := W.head h
    W := W.tail
    let a1 := f l (get Analysis l)
    let a2 := get Analysis l'
    if not (leq a1 a2) then
      Analysis := Analysis.insert l' (join a1 a2)
      for (l'', l''') in F.filter (fun (x, _) => x == l') do
        W := List.cons (l'', l''') W

  -- Step 3: Presenting the result
  let mut result := ∅
  for l in labels do
    result := result.insert ⟨l, .e0⟩ (get Analysis l)
    result := result.insert ⟨l, .e1⟩ (f l (get Analysis l))
  return result

end ProgramAnalysis.DataFlowAnalysis
