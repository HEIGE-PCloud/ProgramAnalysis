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

def expr := expr3

#eval expr.pp

#eval Value.pp <$> (expr.eval ⟨[]⟩)

def example.constraint := expr.constraints.run expr.allFns

#eval example.constraint.toList.map (fun c => c.pp)

def example.solution := Constraint.solve example.constraint.toList

#eval example.solution.toList.map (fun (node, value) => s!"{node.pp} ↦ {value.toList.map (fun t: FnTerm => t.pp)}")

end ProgramAnalysis.ControlFlowAnalysis.Example
