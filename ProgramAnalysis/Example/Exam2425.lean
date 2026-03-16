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

section Question2

open ControlFlowAnalysis
def expr : Expr := [Fun|
  let f = (
    if 1 > 0
      then (fn x => x)
      else (fn y => y)
  )
  in f 2
]

/-- info: (let f = (if (1¹ > 0²)³ then (fn x => x⁴)⁵ else (fn y => y⁶)⁷)⁸ in (f⁹ 2¹⁰)¹¹)¹² -/
#guard_msgs in
#eval IO.println expr

/-- info: (some 2) -/
#guard_msgs in
#eval IO.println (expr.eval .empty)

def constraints := expr.constraints.run expr.allFns
/--
info: [C(5) ⊆ C(8), C(7) ⊆ C(8), C(8) ⊆ r(f), C(11) ⊆ C(12), r(f) ⊆ C(9), r(x) ⊆ C(4), r(y) ⊆ C(6), fn x => x⁴ ⊆ C(5), fn y => y⁶ ⊆ C(7), fn x => x⁴ ⊆ C(9) => C(4) ⊆ C(11), fn x => x⁴ ⊆ C(9) => C(10) ⊆ r(x), fn y => y⁶ ⊆ C(9) => C(6) ⊆ C(11), fn y => y⁶ ⊆ C(9) => C(10) ⊆ r(y)]
-/
#guard_msgs in
#eval IO.println constraints

def solution := Constraint.solve constraints.toList

/--
info: C(4) ↦ []
C(5) ↦ [fn x => x⁴]
C(6) ↦ []
C(7) ↦ [fn y => y⁶]
C(8) ↦ [fn x => x⁴, fn y => y⁶]
C(9) ↦ [fn x => x⁴, fn y => y⁶]
C(10) ↦ []
C(11) ↦ []
C(12) ↦ []
r(f) ↦ [fn x => x⁴, fn y => y⁶]
r(x) ↦ []
r(y) ↦ []
-/
#guard_msgs in
#eval solution.toList.forM (fun (node, value) => IO.println s!"{node} ↦ {value.toList.map (fun t: FnTerm => t)}")

end Question2

end ProgramAnalysis.Example
