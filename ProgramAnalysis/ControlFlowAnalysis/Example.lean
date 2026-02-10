module

import ProgramAnalysis.ControlFlowAnalysis.Basic


namespace ControlFlowAnalysis.Example

def expr1 : Expr := .build <|
  open Expr in
  mkApp (mkFn "x" (mkVar "x")) (mkFn "y" (mkVar "y"))

def expr2 : Expr := .build <|
  open Expr in
  mkLetIn "f₁" (mkFn "x₁" (mkVar "x₁"))
    (mkLetIn "f₂" (mkFn "x₂" (mkVar "x₂"))
    (mkApp (mkApp (mkVar "f₁") (mkVar "f₂")) (mkFn "y" (mkVar "y"))))

def expr3 : Expr := .build <|
  open Expr in
  mkLetIn "f" (mkFn "x" (mkIte (mkOp Op.gt (mkVar "x") (mkConst 0)) (mkFn "y" (mkVar "y")) (mkFn "z" (mkConst 25)))) (mkApp (mkApp (mkVar "f") (mkConst 3)) (mkConst 0))

def expr := expr3

#eval expr.pp

def example.constraints := (Expr.constraints expr).run (Expr.allFns expr)

#eval example.constraints.toList.map (fun c => c.pp)

def example.solution := ControlFlowAnalysis.Constraint.solve example.constraints.toList

#eval example.solution.toList.map (fun (node, value) => s!"{node.pp} ↦ {value.toList.map (fun t: FnTerm => t.pp)}")


end ControlFlowAnalysis.Example
