module

public import ProgramAnalysis.ControlFlowAnalysis
meta import ProgramAnalysis.ControlFlowAnalysis.Meta

namespace ProgramAnalysis.ControlFlowAnalysis.Example

open ProgramAnalysis.ControlFlowAnalysis Fun

-- Example in lecture
def expr1 : Expr := [Fun|(fn x => x)(fn y => y)]

-- Tutorial Sheet 4, Exercise 1
def expr2 : Expr := [Fun|
  let f₁ = fn x₁ => x₁ in
  let f₂ = fn x₂ => x₂ in
  (f₁ f₂) (fn y => y)
]

-- Tutorial Sheet 4, Exercise 2
def expr3 : Expr := [Fun|
  (let f = (fn x => (if (x > 0) then (fn y => y)
                    else (fn z => 25)))
  in ((f 3) 0))
]

def expr4 : Expr := [Fun|
  (let g = (fn f => (if (f 3) then 10 else 5))
   in (g (fn y => (y > 2))))
]

-- Tutorial Sheet 3, Exercise 4
def expr5 : Expr := [Fun|
  (let f = (fn z => 1) in
  (((fn x => x x)(fn y => y)) f))
]

def expr := expr4

/--
info: (let g = (fn f => (if (f¹ 3²)³ then 10⁴ else 5⁵)⁶)⁷ in (g⁸ (fn y => (y⁹ > 2¹⁰)¹¹)¹²)¹³)¹⁴
-/
#guard_msgs in
#eval IO.println expr

/-- info: (some 10) -/
#guard_msgs in
#eval IO.println (expr.eval .empty)

def example.constraint := expr.constraints.run expr.allFns

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
#eval example.constraint.toList.forM IO.println

def example.solution := Constraint.solve example.constraint.toList

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
#eval example.solution.toList.forM (fun (node, value) => IO.println s!"{node} ↦ {value.toList.map (fun t: FnTerm => t)}")

end ProgramAnalysis.ControlFlowAnalysis.Example
