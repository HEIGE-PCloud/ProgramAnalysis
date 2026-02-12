module

public import ProgramAnalysis.DataFlowAnalysis.While
public import Batteries.Data.List

namespace ProgramAnalysis.DataFlowAnalysis

namespace AvailableExpression
open While

def kill' : Block → ReaderM Stmt (List AExp)
  | .assign x _ _ => do
    let stmt ← read
    let aexps := stmt.aexp
    pure (aexps.filter (fun a' => a'.FV.elem x))
  | .skip _ => pure ∅
  | .test _ _ => pure ∅

def kill (s : Stmt) (b : Block) : List AExp := (kill' b).run s

def gen' : Block → ReaderM Stmt (List AExp)
  | .assign x a _ => pure (a.aexp.filter (fun a' => !(a'.FV.elem x)))
  | .skip _ => pure []
  | .test b _ => pure b.aexp

def gen (s : Stmt) (b : Block) : List AExp := (gen' b).run s

public inductive EquationType
  | entry
  | exit
deriving BEq, Repr

def EquationType.pp (e : EquationType) : String :=
  match e with
    | entry => "entry"
    | exit => "exit"

public structure EquationAtom where
  label : Label
  ty : EquationType
deriving BEq, Repr

def EquationAtom.pp (e : EquationAtom) : String := s!"AE {e.ty.pp} ({e.label})"

public inductive SetEquation where
  | empty : SetEquation
  | var : EquationAtom → SetEquation
  | list : List AExp → SetEquation
  | union : SetEquation → SetEquation → SetEquation
  | inter : SetEquation → SetEquation → SetEquation
  | diff : SetEquation → SetEquation → SetEquation
deriving Repr

-- def SetEquation.pp : SetEquation → String

public def inters : List SetEquation → SetEquation
  | [] => .empty
  | x :: xs => .inter x (inters xs)

public structure Equation where
  lhs : EquationAtom
  rhs : SetEquation
deriving Repr

public def Equation.build (s : Stmt) (l : Label) (ty : EquationType) : Equation :=
  let lhs := EquationAtom.mk l ty
  let b := s.block! l
  match ty with
    | .entry => if l = s.init then
      ⟨lhs, .empty⟩
    else
      ⟨lhs, inters (s.flow.map (fun (_l, l') => .var (EquationAtom.mk l' .exit)))⟩
    | .exit => ⟨lhs, .union (.diff (.var ⟨l, .entry⟩) (.list (kill s b))) (.list (gen s b))⟩

public def Equation.buildAll (s : Stmt) : List Equation :=
  s.labels.flatMap (fun l => [Equation.build s l .entry, Equation.build s l .exit])

end AvailableExpression

end ProgramAnalysis.DataFlowAnalysis
