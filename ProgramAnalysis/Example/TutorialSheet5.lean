module
import ProgramAnalysis.DataFlowAnalysis
meta import ProgramAnalysis.DataFlowAnalysis
import ProgramAnalysis.ControlFlowAnalysis
meta import ProgramAnalysis.ControlFlowAnalysis

namespace ProgramAnalysis.Example

section Exercise2

open ControlFlowAnalysis

def expr : Expr := [Fun|
(let g = (fn f => (if (f 3) then 10 else 5))
in (g (fn y => (y > 2))))
]

/--
info: (let g = (fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶)⁷ in (g⁸ (fn y => (y⁹ > 2¹⁰)¹¹)¹²)¹³)¹⁴
-/
#guard_msgs in
#eval IO.println expr

def constraints := expr.constraints'

/--
info: C(4) ⊆ C(6)
C(5) ⊆ C(6)
C(7) ⊆ r(g)
C(13) ⊆ C(14)
r(f) ⊆ C(1)
r(g) ⊆ C(8)
r(y) ⊆ C(9)
fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶ ⊆ C(7)
fn y => (y⁹ > 2¹⁰)¹¹ ⊆ C(12)
fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶ ⊆ C(1) => C(2) ⊆ r(f)
fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶ ⊆ C(1) => C(6) ⊆ C(3)
fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶ ⊆ C(8) => C(6) ⊆ C(13)
fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶ ⊆ C(8) => C(12) ⊆ r(f)
fn y => (y⁹ > 2¹⁰)¹¹ ⊆ C(1) => C(2) ⊆ r(y)
fn y => (y⁹ > 2¹⁰)¹¹ ⊆ C(1) => C(11) ⊆ C(3)
fn y => (y⁹ > 2¹⁰)¹¹ ⊆ C(8) => C(11) ⊆ C(13)
fn y => (y⁹ > 2¹⁰)¹¹ ⊆ C(8) => C(12) ⊆ r(y)
-/
#guard_msgs in
#eval constraints.forM IO.println

def solution := Constraint.solve constraints.toList

/--
info: C(1) ↦ [fn y => (y⁹ > 2¹⁰)¹¹]
C(2) ↦ []
C(3) ↦ []
C(4) ↦ []
C(5) ↦ []
C(6) ↦ []
C(7) ↦ [fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶]
C(8) ↦ [fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶]
C(9) ↦ []
C(11) ↦ []
C(12) ↦ [fn y => (y⁹ > 2¹⁰)¹¹]
C(13) ↦ []
C(14) ↦ []
r(f) ↦ [fn y => (y⁹ > 2¹⁰)¹¹]
r(g) ↦ [fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶]
r(y) ↦ []
-/
#guard_msgs in
#eval solution.toList.forM (fun (node, value) => IO.println s!"{node} ↦ {value.toList.map (fun t: FnTerm => t)}")

end Exercise2

end ProgramAnalysis.Example
