module

import ProgramAnalysis.DataFlowAnalysis

namespace ProgramAnalysis.DataFlowAnalysis.Example

open ProgramAnalysis.DataFlowAnalysis While

section AE

def example1 : Stmt := [While|
  x := a + b;
  y := a * b;
  while y > a + b do (
    a := a + 1;
    x := a + b
  )
]

#eval example1

def equations := AvailableExpression.equations example1

#eval equations.forM (fun eq => IO.println eq.toString)

def solution := chaoticIteration equations AvailableExpression.init

#eval solution.toList.forM
  (fun (k, v) => IO.println s!"{k} = {v.toList.map (fun a: AExp => a.toString)}")

end AE


end ProgramAnalysis.DataFlowAnalysis.Example
