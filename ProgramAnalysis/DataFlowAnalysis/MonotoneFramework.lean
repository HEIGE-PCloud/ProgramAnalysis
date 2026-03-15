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
  value : Type
  leq : value → value → Bool
  join : value → value → value
  bot : Stmt → value
  extremeValue : Stmt → value
  extremeLabel : Stmt → Std.TreeSet Label
  flow : Stmt → List (Label × Label)
  transfer : Stmt → Label → value → value

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
deriving DecidableEq, Repr, Ord

public inductive Equation.Expr (value : Type) where
  | bot : Equation.Expr value
  | lit : value → Equation.Expr value
  | atom : Equation.Atom → Equation.Expr value
  | join : Equation.Expr value → Equation.Expr value → Equation.Expr value
  | app : (value → value) → Equation.Atom → Equation.Expr value

public structure Equation (value : Type) : Type where
  lhs : Equation.Atom
  rhs : Equation.Expr value

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

end ProgramAnalysis.DataFlowAnalysis
