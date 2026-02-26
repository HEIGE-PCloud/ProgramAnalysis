module

import ProgramAnalysis.DataFlowAnalysis

namespace ProgramAnalysis.DataFlowAnalysis.Example

open ProgramAnalysis.DataFlowAnalysis While

namespace AE

def exampleAE : Stmt := [While|
  x := a + b;
  y := a * b;
  while y > a + b do (
    a := a + 1;
    x := a + b
  )
]

#eval exampleAE

def equations := AvailableExpression.equations exampleAE

#eval equations.forM (fun eq => IO.println eq.toString)

def solution := chaoticIteration equations (AvailableExpression.init exampleAE)

#eval solution.toList.forM
  (fun (k, v) => IO.println s!"{k} = {v.toList.map (fun a: AExp => a.toString)}")

end AE

namespace RD

def exampleRD : Stmt := [While|
  x := 5;
  y := 1;
  while x > 1 do (
    y := x * y;
    x := x - 1
  )
]

def equations := ReachingDefinition.equations exampleRD

#eval equations.forM (fun eq => IO.println eq.toString)

def solution := chaoticIteration equations ReachingDefinition.init

#eval solution.toList.forM
  (fun (k, v) => IO.println s!"{k} = {v.toList}")

end RD

end ProgramAnalysis.DataFlowAnalysis.Example
