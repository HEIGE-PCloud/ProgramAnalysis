module

public import ProgramAnalysis.ControlFlowAnalysis

namespace ProgramAnalysis.ControlFlowAnalysis.Example

open ProgramAnalysis.ControlFlowAnalysis Fun

-- Example in lecture
def expr1 : Expr := .build <|
  open Expr in
  mkApp (mkFn "x" (mkVar "x")) (mkFn "y" (mkVar "y"))

-- Tutorial Sheet 4, Exercise 1
def expr2 : Expr := Expr.build <|
  open Expr in
  mkLetIn "f₁" (mkFn "x₁" (mkVar "x₁"))
    (mkLetIn "f₂" (mkFn "x₂" (mkVar "x₂"))
    (mkApp (mkApp (mkVar "f₁") (mkVar "f₂")) (mkFn "y" (mkVar "y"))))

def expr := expr2

#eval expr.pp

def example.constraint := (expr.constraints).run (expr.allFns)

#eval example.constraint.toList.map (fun c => c.pp)

def example.solution := ControlFlowAnalysis.Constraint.solve example.constraint.toList

#eval example.solution.toList.map (fun (node, value) => s!"{node.pp} ↦ {value.toList.map (fun t: FnTerm => t.pp)}")

end ProgramAnalysis.ControlFlowAnalysis.Example
