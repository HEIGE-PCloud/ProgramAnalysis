module

import ProgramAnalysis.DataFlowAnalysis

namespace ProgramAnalysis.DataFlowAnalysis

namespace AvailableExpression

def program : Stmt := [While|
  x := a + b;
  y := a * b;
  while y > a + b do (
    a := a + 1;
    x := a + b
  )
]

def solution := analysis.worklistAlgorithm program

/--
info: AE◦(1) = []
AE•(1) = [(a + b)]
AE◦(2) = [(a + b)]
AE•(2) = [(a + b), (a * b)]
AE◦(3) = [(a + b)]
AE•(3) = [(a + b)]
AE◦(4) = [(a + b)]
AE•(4) = []
AE◦(5) = []
AE•(5) = [(a + b)]
-/
#guard_msgs in
#eval println solution

end AvailableExpression

namespace ReachingDefinition

def program : Stmt := [While|
  x := 5;
  y := 1;
  while x > 1 do (
    y := x * y;
    x := x - 1
  )
]

def solution := analysis.worklistAlgorithm program

/--
info: RD◦(1) = [(x, ?), (y, ?)]
RD•(1) = [(x, 1), (y, ?)]
RD◦(2) = [(x, 1), (y, ?)]
RD•(2) = [(x, 1), (y, 2)]
RD◦(3) = [(x, 1), (x, 5), (y, 2), (y, 4)]
RD•(3) = [(x, 1), (x, 5), (y, 2), (y, 4)]
RD◦(4) = [(x, 1), (x, 5), (y, 2), (y, 4)]
RD•(4) = [(x, 1), (x, 5), (y, 4)]
RD◦(5) = [(x, 1), (x, 5), (y, 4)]
RD•(5) = [(x, 5), (y, 4)]
-/
#guard_msgs in
#eval println solution

end ReachingDefinition

namespace VeryBusyExpression

def program : Stmt := [While|
  if a > b then
    x := b - a;
    y := a - b
  else
    y := b - a;
    x := a - b
  ]

def solution := analysis.worklistAlgorithm program

/--
info: VB◦(1) = [(a - b), (b - a)]
VB•(1) = [(a - b), (b - a)]
VB◦(2) = [(a - b)]
VB•(2) = [(a - b), (b - a)]
VB◦(3) = []
VB•(3) = [(a - b)]
VB◦(4) = [(a - b)]
VB•(4) = [(a - b), (b - a)]
VB◦(5) = []
VB•(5) = [(a - b)]
-/
#guard_msgs in
#eval println solution

end VeryBusyExpression

namespace LiveVariable

def program : Stmt := [While|
  x := 2;
  y := 4;
  x := 1;
  (if y > x then z := y else z := y * y);
  x := z
]

def solution := analysis.worklistAlgorithm program

/--
info: LV◦(1) = []
LV•(1) = []
LV◦(2) = [y]
LV•(2) = []
LV◦(3) = [x, y]
LV•(3) = [y]
LV◦(4) = [y]
LV•(4) = [x, y]
LV◦(5) = [z]
LV•(5) = [y]
LV◦(6) = [z]
LV•(6) = [y]
LV◦(7) = []
LV•(7) = [z]
-/
#guard_msgs in
#eval println solution

end LiveVariable


namespace Tutorial2Q1

def program : Stmt := [While|
  x := 1;
  while y > 0 do (x := x - 1);
  x := 2
]

def solution := LiveVariable.analysis.worklistAlgorithm program

/--
info: LV◦(1) = [x, y]
LV•(1) = [y]
LV◦(2) = [x, y]
LV•(2) = [x, y]
LV◦(3) = [x, y]
LV•(3) = [x, y]
LV◦(4) = []
LV•(4) = []
-/
#guard_msgs in
#eval println solution

end Tutorial2Q1

namespace ConstantPropagation

def program : Stmt := [While|
  y := 2;
  (if z > 1 then x := 1 else x := -1);
  y := x * x
]

def solution := analysis.worklistAlgorithm program

/--
info: CP◦(1) = [(x, ⊤), (y, ⊤), (z, ⊤)]
CP•(1) = [(x, ⊤), (y, 2), (z, ⊤)]
CP◦(2) = [(x, ⊤), (y, 2), (z, ⊤)]
CP•(2) = [(x, ⊤), (y, 2), (z, ⊤)]
CP◦(3) = [(x, ⊤), (y, 2), (z, ⊤)]
CP•(3) = [(x, 1), (y, 2), (z, ⊤)]
CP◦(4) = [(x, ⊤), (y, 2), (z, ⊤)]
CP•(4) = [(x, -1), (y, 2), (z, ⊤)]
CP◦(5) = [(x, ⊤), (y, 2), (z, ⊤)]
CP•(5) = [(x, ⊤), (y, ⊤), (z, ⊤)]
-/
#guard_msgs in
#eval println solution

end ConstantPropagation

end ProgramAnalysis.DataFlowAnalysis
