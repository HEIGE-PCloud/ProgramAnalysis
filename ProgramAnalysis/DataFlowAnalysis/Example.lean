module

import ProgramAnalysis.DataFlowAnalysis

namespace ProgramAnalysis.DataFlowAnalysis.Example

open ProgramAnalysis.DataFlowAnalysis While AvailableExpression

def example1 : Stmt := [While|
  x := a + b;
  y := a * b;
  while y > a + b do (
    a := a + 1;
    x := a + b
  )
]

#eval example1

def equations := Equation.buildAll example1
#eval equations.map (fun eq => eq.toString)

def init := chaoticIter (chaoticInit equations) equations
#eval init

def solution := chaoticIters equations
#eval solution.toList.map (fun (k, v) => s!"{k} = {v.toList.map (fun a: AExp => a.toString)}")

end ProgramAnalysis.DataFlowAnalysis.Example
