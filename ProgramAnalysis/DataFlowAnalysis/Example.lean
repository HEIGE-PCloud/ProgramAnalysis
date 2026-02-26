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

def equations := AE.equations example1
#eval equations.map (fun eq => eq.toString)

def solution := chaoticIteration equations AE.init
#eval solution.toList.map
  (fun (k, v) => s!"{k} = {v.toList.map (fun a: AExp => a.toString)}")

end ProgramAnalysis.DataFlowAnalysis.Example
