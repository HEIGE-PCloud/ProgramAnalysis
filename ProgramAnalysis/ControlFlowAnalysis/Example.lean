module

public import ProgramAnalysis.ControlFlowAnalysis
meta import ProgramAnalysis.ControlFlowAnalysis.Meta

namespace ProgramAnalysis.ControlFlowAnalysis.Example

open ProgramAnalysis.ControlFlowAnalysis Fun

-- Example in lecture
def expr1 : Expr := (fun|(fn x => x)(fn y => y))

-- Tutorial Sheet 4, Exercise 1
def expr2 : Expr := (fun|
  let f₁ = fn x₁ => x₁ in
  let f₂ = fn x₂ => x₂ in
  (f₁ f₂) (fn y => y)
)

def expr := expr2

#eval expr.pp

def example.constraint := (expr.constraints).run (expr.allFns)

#eval example.constraint.toList.map (fun c => c.pp)

def example.solution := ControlFlowAnalysis.Constraint.solve example.constraint.toList

/-
["C(1) ↦ [fn x₂ => x₂³]", "C(2) ↦ [fn x₁ => x₁¹]", "C(3) ↦ [fn y => y⁸]", "C(4) ↦ [fn x₂ => x₂³]",
  "C(5) ↦ [fn x₁ => x₁¹]", "C(6) ↦ [fn x₂ => x₂³]", "C(7) ↦ [fn x₂ => x₂³]", "C(8) ↦ []", "C(9) ↦ [fn y => y⁸]",
  "C(10) ↦ [fn y => y⁸]", "C(11) ↦ [fn y => y⁸]", "C(12) ↦ [fn y => y⁸]", "r(f₁) ↦ [fn x₁ => x₁¹]",
  "r(f₂) ↦ [fn x₂ => x₂³]", "r(x₁) ↦ [fn x₂ => x₂³]", "r(x₂) ↦ [fn y => y⁸]", "r(y) ↦ []"]
-/
#eval example.solution.toList.map (fun (node, value) => s!"{node.pp} ↦ {value.toList.map (fun t: FnTerm => t.pp)}")

end ProgramAnalysis.ControlFlowAnalysis.Example
