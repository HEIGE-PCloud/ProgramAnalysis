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

def equations := Equation.buildAll example1
#eval equations

-- FIXME: this is not correct
def solution := chaoticIters equations
#eval solution

end ProgramAnalysis.DataFlowAnalysis.Example
