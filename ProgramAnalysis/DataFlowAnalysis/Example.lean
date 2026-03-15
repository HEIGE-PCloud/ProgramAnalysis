module

import ProgramAnalysis.DataFlowAnalysis

namespace ProgramAnalysis.DataFlowAnalysis

open While

namespace AvailableExpression

def exampleAE : Stmt := [While|
  x := a + b;
  y := a * b;
  while y > a + b do (
    a := a + 1;
    x := a + b
  )
]

def equations := analysis.equations exampleAE


/--
info: Analysis◦(1) = {}
Analysis•(1) = ((Analysis◦(1) \ {}) ∪ {(a + b)})
Analysis◦(2) = Analysis•(1)
Analysis•(2) = ((Analysis◦(2) \ {}) ∪ {(a * b)})
Analysis◦(3) = (Analysis•(5) ∩ Analysis•(2))
Analysis•(3) = ((Analysis◦(3) \ {}) ∪ {})
Analysis◦(4) = Analysis•(3)
Analysis•(4) = ((Analysis◦(4) \ {(a + b), (a + 1), (a * b)}) ∪ {})
Analysis◦(5) = Analysis•(4)
Analysis•(5) = ((Analysis◦(5) \ {}) ∪ {(a + b)})
-/
#guard_msgs in
#eval equations.forM IO.println

def solution := chaoticIteration equations (analysis.init exampleAE)

/--
info: Analysis◦(1) = []
Analysis•(1) = [(a + b)]
Analysis◦(2) = [(a + b)]
Analysis•(2) = [(a + b), (a * b)]
Analysis◦(3) = [(a + b)]
Analysis•(3) = [(a + b)]
Analysis◦(4) = [(a + b)]
Analysis•(4) = []
Analysis◦(5) = []
Analysis•(5) = [(a + b)]
-/
#guard_msgs in
#eval println solution

end AvailableExpression

namespace ReachingDefinition

def exampleRD : Stmt := [While|
  x := 5;
  y := 1;
  while x > 1 do (
    y := x * y;
    x := x - 1
  )
]

def equations := analysis.equations exampleRD

/--
info: Analysis◦(1) = {(x, ?), (y, ?)}
Analysis•(1) = ((Analysis◦(1) \ {(x, ?), (x, 1), (x, 5)}) ∪ {(x, 1)})
Analysis◦(2) = Analysis•(1)
Analysis•(2) = ((Analysis◦(2) \ {(y, ?), (y, 2), (y, 4)}) ∪ {(y, 2)})
Analysis◦(3) = (Analysis•(5) ∪ Analysis•(2))
Analysis•(3) = ((Analysis◦(3) \ {}) ∪ {})
Analysis◦(4) = Analysis•(3)
Analysis•(4) = ((Analysis◦(4) \ {(y, ?), (y, 2), (y, 4)}) ∪ {(y, 4)})
Analysis◦(5) = Analysis•(4)
Analysis•(5) = ((Analysis◦(5) \ {(x, ?), (x, 1), (x, 5)}) ∪ {(x, 5)})
-/
#guard_msgs in
#eval equations.forM IO.println

def solution := chaoticIteration equations (analysis.init exampleRD)

/--
info: Analysis◦(1) = [(x, ?), (y, ?)]
Analysis•(1) = [(x, 1), (y, ?)]
Analysis◦(2) = [(x, 1), (y, ?)]
Analysis•(2) = [(x, 1), (y, 2)]
Analysis◦(3) = [(x, 1), (x, 5), (y, 2), (y, 4)]
Analysis•(3) = [(x, 1), (x, 5), (y, 2), (y, 4)]
Analysis◦(4) = [(x, 1), (x, 5), (y, 2), (y, 4)]
Analysis•(4) = [(x, 1), (x, 5), (y, 4)]
Analysis◦(5) = [(x, 1), (x, 5), (y, 4)]
Analysis•(5) = [(x, 5), (y, 4)]
-/
#guard_msgs in
#eval println solution

end ReachingDefinition

namespace VeryBusyExpression

def exampleVB : Stmt := [While|
  if a > b then
    x := b - a;
    y := a - b
  else
    y := b - a;
    x := a - b
  ]

def equations := analysis.equations exampleVB

/--
info: Analysis◦(1) = (Analysis•(2) ∩ Analysis•(4))
Analysis•(1) = ((Analysis◦(1) \ {}) ∪ {})
Analysis◦(2) = Analysis•(3)
Analysis•(2) = ((Analysis◦(2) \ {}) ∪ {(b - a)})
Analysis◦(3) = {}
Analysis•(3) = ((Analysis◦(3) \ {}) ∪ {(a - b)})
Analysis◦(4) = Analysis•(5)
Analysis•(4) = ((Analysis◦(4) \ {}) ∪ {(b - a)})
Analysis◦(5) = {}
Analysis•(5) = ((Analysis◦(5) \ {}) ∪ {(a - b)})
-/
#guard_msgs in
#eval equations.forM IO.println

def solution := chaoticIteration equations (analysis.init exampleVB)

/--
info: Analysis◦(1) = [(a - b), (b - a)]
Analysis•(1) = [(a - b), (b - a)]
Analysis◦(2) = [(a - b)]
Analysis•(2) = [(a - b), (b - a)]
Analysis◦(3) = []
Analysis•(3) = [(a - b)]
Analysis◦(4) = [(a - b)]
Analysis•(4) = [(a - b), (b - a)]
Analysis◦(5) = []
Analysis•(5) = [(a - b)]
-/
#guard_msgs in
#eval println solution

end VeryBusyExpression

namespace LiveVariable

def exampleLV : Stmt := [While|
  x := 2;
  y := 4;
  x := 1;
  (if y > x then z := y else z := y * y);
  x := z
]

def equations := analysis.equations exampleLV

/--
info: Analysis◦(1) = Analysis•(2)
Analysis•(1) = ((Analysis◦(1) \ {x}) ∪ {})
Analysis◦(2) = Analysis•(3)
Analysis•(2) = ((Analysis◦(2) \ {y}) ∪ {})
Analysis◦(3) = Analysis•(4)
Analysis•(3) = ((Analysis◦(3) \ {x}) ∪ {})
Analysis◦(4) = (Analysis•(5) ∪ Analysis•(6))
Analysis•(4) = ((Analysis◦(4) \ {}) ∪ {x, y})
Analysis◦(5) = Analysis•(7)
Analysis•(5) = ((Analysis◦(5) \ {z}) ∪ {y})
Analysis◦(6) = Analysis•(7)
Analysis•(6) = ((Analysis◦(6) \ {z}) ∪ {y})
Analysis◦(7) = {}
Analysis•(7) = ((Analysis◦(7) \ {x}) ∪ {z})
-/
#guard_msgs in
#eval equations.forM IO.println

def solution := chaoticIteration equations (analysis.init exampleLV)

/--
info: Analysis◦(1) = []
Analysis•(1) = []
Analysis◦(2) = [y]
Analysis•(2) = []
Analysis◦(3) = [x, y]
Analysis•(3) = [y]
Analysis◦(4) = [y]
Analysis•(4) = [x, y]
Analysis◦(5) = [z]
Analysis•(5) = [y]
Analysis◦(6) = [z]
Analysis•(6) = [y]
Analysis◦(7) = []
Analysis•(7) = [z]
-/
#guard_msgs in
#eval println solution

end LiveVariable

namespace Exam2425Q1

open ReachingDefinition

def program : Stmt := [While|
  x := 0;
  (if x < y
    then y := x
    else (while y < 0 do (y := x)));
  x := y + x
]

/--
info: [x := 0]¹;
if [(x < y)]² then ([y := x]³) else (while [(y < 0)]⁴ do ([y := x]⁵));
[x := (y + x)]⁶
-/
#guard_msgs in
#eval IO.println program.toString

/-- info: [(4, 5), (5, 4), (2, 3), (2, 4), (3, 6), (4, 6), (1, 2)] -/
#guard_msgs in
#eval program.flow

def equations := analysis.equations program

/--
info: Analysis◦(1) = {(x, ?), (y, ?)}
Analysis•(1) = ((Analysis◦(1) \ {(x, ?), (x, 1), (x, 6)}) ∪ {(x, 1)})
Analysis◦(2) = Analysis•(1)
Analysis•(2) = ((Analysis◦(2) \ {}) ∪ {})
Analysis◦(3) = Analysis•(2)
Analysis•(3) = ((Analysis◦(3) \ {(y, ?), (y, 3), (y, 5)}) ∪ {(y, 3)})
Analysis◦(4) = (Analysis•(5) ∪ Analysis•(2))
Analysis•(4) = ((Analysis◦(4) \ {}) ∪ {})
Analysis◦(5) = Analysis•(4)
Analysis•(5) = ((Analysis◦(5) \ {(y, ?), (y, 3), (y, 5)}) ∪ {(y, 5)})
Analysis◦(6) = (Analysis•(3) ∪ Analysis•(4))
Analysis•(6) = ((Analysis◦(6) \ {(x, ?), (x, 1), (x, 6)}) ∪ {(x, 6)})
-/
#guard_msgs in
#eval equations.forM IO.println

def solution := chaoticIteration equations (analysis.init program)

/--
info: Analysis◦(1) = [(x, ?), (y, ?)]
Analysis•(1) = [(x, 1), (y, ?)]
Analysis◦(2) = [(x, 1), (y, ?)]
Analysis•(2) = [(x, 1), (y, ?)]
Analysis◦(3) = [(x, 1), (y, ?)]
Analysis•(3) = [(x, 1), (y, 3)]
Analysis◦(4) = [(x, 1), (y, ?), (y, 5)]
Analysis•(4) = [(x, 1), (y, ?), (y, 5)]
Analysis◦(5) = [(x, 1), (y, ?), (y, 5)]
Analysis•(5) = [(x, 1), (y, 5)]
Analysis◦(6) = [(x, 1), (y, ?), (y, 3), (y, 5)]
Analysis•(6) = [(x, 6), (y, ?), (y, 3), (y, 5)]
-/
#guard_msgs in
#eval println solution

end Exam2425Q1

namespace Tutorial2Q1

def program : Stmt := [While|
  x := 1;
  while y > 0 do (x := x - 1);
  x := 2
]

open LiveVariable

def equations := analysis.equations program

/--
info: Analysis◦(1) = Analysis•(2)
Analysis•(1) = ((Analysis◦(1) \ {x}) ∪ {})
Analysis◦(2) = (Analysis•(3) ∪ Analysis•(4))
Analysis•(2) = ((Analysis◦(2) \ {}) ∪ {y})
Analysis◦(3) = Analysis•(2)
Analysis•(3) = ((Analysis◦(3) \ {x}) ∪ {x})
Analysis◦(4) = {}
Analysis•(4) = ((Analysis◦(4) \ {x}) ∪ {})
-/
#guard_msgs in
#eval equations.forM IO.println

def solution := chaoticIteration equations (analysis.init program)

/--
info: Analysis◦(1) = [x, y]
Analysis•(1) = [y]
Analysis◦(2) = [x, y]
Analysis•(2) = [x, y]
Analysis◦(3) = [x, y]
Analysis•(3) = [x, y]
Analysis◦(4) = []
Analysis•(4) = []
-/
#guard_msgs in
#eval println solution

end Tutorial2Q1

end ProgramAnalysis.DataFlowAnalysis
