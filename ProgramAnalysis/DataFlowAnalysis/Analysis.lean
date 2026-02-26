module

public import ProgramAnalysis.DataFlowAnalysis.While
public import Batteries.Data.List
public import Std.Data.TreeSet
public import Std.Data.TreeMap
public import ProgramAnalysis.DataFlowAnalysis.Equation

namespace ProgramAnalysis.DataFlowAnalysis

namespace AvailableExpression
open While

def AE.kill (stmt : Stmt) : Block → List AExp
  | .assign x _ _ => stmt.aexp.filter (fun a' => a'.FV.elem x)
  | _ => ∅

def AE.gen (_ : Stmt) : Block → List AExp
  | .assign x a _ => a.aexp.filter (fun a' => !(a'.FV.elem x))
  | _ => ∅

def AE.entry (s : Stmt) (l : Label) : Equation AExp :=
  let lhs := Equation.Atom.mk l .e0
  if l = s.init then ⟨lhs, .empty⟩
  else ⟨lhs, inters ((s.flow.filter (fun (_, ll) => l == ll)).map (fun (l', _l) => .var (Equation.Atom.mk l' .e1)))⟩

def AE.exit (s : Stmt) (l : Label) : Equation AExp :=
  let lhs := Equation.Atom.mk l .e1
  let b := s.block! l
  ⟨lhs, .union (.diff (.var ⟨l, .e0⟩) (.lit (.ofList (kill s b)))) (.lit (.ofList (gen s b)))⟩

public def AE.equations (s : Stmt) : List (Equation AExp) :=
  s.labels.flatMap (fun l => [AE.entry s l, AE.exit s l])

public def AE.init [Ord α] (es : List (Equation α))
  : Std.TreeMap Equation.Atom (Std.TreeSet α) :=
  es.foldl (fun acc eq => acc.insert eq.lhs .empty) .empty

end AvailableExpression

end ProgramAnalysis.DataFlowAnalysis
