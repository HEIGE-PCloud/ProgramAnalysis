module

public import ProgramAnalysis.DataFlowAnalysis.While
public import Batteries.Data.List
public import Std.Data.TreeSet
public import Std.Data.TreeMap
public import ProgramAnalysis.DataFlowAnalysis.Equation

namespace ProgramAnalysis.DataFlowAnalysis

namespace AvailableExpression
open While

def AE.kill' : Block → ReaderM Stmt (List AExp)
  | .assign x _ _ => do
    let stmt ← read
    let aexps := stmt.aexp
    pure (aexps.filter (fun a' => a'.FV.elem x))
  | .skip _ => pure ∅
  | .test _ _ => pure ∅

def AE.kill (s : Stmt) (b : Block) : List AExp := (kill' b).run s

def AE.gen' : Block → ReaderM Stmt (List AExp)
  | .assign x a _ => pure (a.aexp.filter (fun a' => !(a'.FV.elem x)))
  | .skip _ => pure []
  | .test _ _ => pure []

def AE.gen (s : Stmt) (b : Block) : List AExp := (gen' b).run s

def AE.entry (s : Stmt) (l : Label) : Equation :=
  let lhs := Equation.Atom.mk l .e0
  if l = s.init then ⟨lhs, .empty⟩
  else ⟨lhs, inters ((s.flow.filter (fun (_, ll) => l == ll)).map (fun (l', _l) => .var (Equation.Atom.mk l' .e1)))⟩

def AE.exit (s : Stmt) (l : Label) : Equation :=
  let lhs := Equation.Atom.mk l .e1
  let b := s.block! l
  ⟨lhs, .union (.diff (.var ⟨l, .e0⟩) (.lit (.ofList (kill s b)))) (.lit (.ofList (gen s b)))⟩

public def AE.equations (s : Stmt) : List Equation :=
  s.labels.flatMap (fun l => [AE.entry s l, AE.exit s l])

end AvailableExpression

end ProgramAnalysis.DataFlowAnalysis
