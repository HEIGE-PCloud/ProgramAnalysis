module
import ProgramAnalysis.DataFlowAnalysis
meta import ProgramAnalysis.DataFlowAnalysis
import ProgramAnalysis.ControlFlowAnalysis
meta import ProgramAnalysis.ControlFlowAnalysis

namespace ProgramAnalysis.Example

section Question1

open DataFlowAnalysis

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
#eval IO.println program

/-- info: [(4, 5), (5, 4), (2, 3), (2, 4), (3, 6), (4, 6), (1, 2)] -/
#guard_msgs in
#eval program.flow

def RDsolution := ReachingDefinition.analysis.worklistAlgorithm program

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
#eval println RDsolution

def CPsolution := ConstantPropagation.analysis.worklistAlgorithm program

/--
info: Analysis◦(1) = [(x, ⊤), (y, ⊤)]
Analysis•(1) = [(x, 0), (y, ⊤)]
Analysis◦(2) = [(x, 0), (y, ⊤)]
Analysis•(2) = [(x, 0), (y, ⊤)]
Analysis◦(3) = [(x, 0), (y, ⊤)]
Analysis•(3) = [(x, 0), (y, 0)]
Analysis◦(4) = [(x, 0), (y, ⊤)]
Analysis•(4) = [(x, 0), (y, ⊤)]
Analysis◦(5) = [(x, 0), (y, ⊤)]
Analysis•(5) = [(x, 0), (y, 0)]
Analysis◦(6) = [(x, 0), (y, ⊤)]
Analysis•(6) = [(x, ⊤), (y, ⊤)]
-/
#guard_msgs in
#eval println CPsolution

end Question1

end ProgramAnalysis.Example
