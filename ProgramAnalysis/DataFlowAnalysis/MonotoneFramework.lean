module
import Mathlib.Data.Finset.Basic

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
instance {X : Type} : PartialOrder (Finset X) where
  leq A B            := A ⊆ B
  refl A             := Finset.Subset.refl A
  trans _ _ _ h1 h2  := Finset.Subset.trans h1 h2
  antisymm _ _ h1 h2 := Finset.Subset.antisymm h1 h2

end ProgramAnalysis.DataFlowAnalysis
