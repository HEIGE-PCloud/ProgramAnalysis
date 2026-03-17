module
import ProgramAnalysis.DataFlowAnalysis
meta import ProgramAnalysis.DataFlowAnalysis
import ProgramAnalysis.ControlFlowAnalysis
meta import ProgramAnalysis.ControlFlowAnalysis

namespace ProgramAnalysis.Example

section Question2

open ControlFlowAnalysis
def expr : Expr := [Fun|
  let f = (
    fn x => x
  )
  in (
    let f = fn y => y + 1
    in f 3
  )
]

/-- info: (let f = (fn x => x¹)² in (let f = (fn y => (y³ + 1⁴)⁵)⁶ in (f⁷ 3⁸)⁹)¹⁰)¹¹ -/
#guard_msgs in
#eval IO.println expr

/-- info: (some 4) -/
#guard_msgs in
#eval IO.println (expr.eval .empty)

def constraints := expr.constraints.run expr.allFns
/--
info: C(2) ⊆ r(f)
C(6) ⊆ r(f)
C(9) ⊆ C(10)
C(10) ⊆ C(11)
r(f) ⊆ C(7)
r(x) ⊆ C(1)
r(y) ⊆ C(3)
fn x => x¹ ⊆ C(2)
fn y => (y³ + 1⁴)⁵ ⊆ C(6)
fn x => x¹ ⊆ C(7) => C(1) ⊆ C(9)
fn x => x¹ ⊆ C(7) => C(8) ⊆ r(x)
fn y => (y³ + 1⁴)⁵ ⊆ C(7) => C(5) ⊆ C(9)
fn y => (y³ + 1⁴)⁵ ⊆ C(7) => C(8) ⊆ r(y)
-/
#guard_msgs in
#eval constraints.forM IO.println

def solution := Constraint.solve constraints.toList

/--
info: C(1) ↦ []
C(2) ↦ [fn x => x¹]
C(3) ↦ []
C(5) ↦ []
C(6) ↦ [fn y => (y³ + 1⁴)⁵]
C(7) ↦ [fn x => x¹, fn y => (y³ + 1⁴)⁵]
C(8) ↦ []
C(9) ↦ []
C(10) ↦ []
C(11) ↦ []
r(f) ↦ [fn x => x¹, fn y => (y³ + 1⁴)⁵]
r(x) ↦ []
r(y) ↦ []
-/
#guard_msgs in
#eval solution.toList.forM (fun (node, value) => IO.println s!"{node} ↦ {value.toList.map (fun t: FnTerm => t)}")

end Question2

end ProgramAnalysis.Example
