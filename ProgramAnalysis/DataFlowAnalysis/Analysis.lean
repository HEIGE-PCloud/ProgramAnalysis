module

public import ProgramAnalysis.DataFlowAnalysis.While
public import Batteries.Data.List
public import Std.Data.TreeSet
public import Std.Data.TreeMap
public import ProgramAnalysis.DataFlowAnalysis.Equation

namespace ProgramAnalysis.DataFlowAnalysis

open While

namespace AvailableExpression

@[expose] public def Value := AExp
  deriving Ord

def kill (stmt : Stmt) : Block → List Value
  | .assign x _ _ => stmt.aexp.filter (fun a' => a'.FV.elem x)
  | _ => ∅

def gen : Block → List Value
  | .assign x a _ => a.aexp.filter (fun a' => !(a'.FV.elem x))
  | _ => ∅

def entry (s : Stmt) (l : Label) : Equation Value :=
  let lhs := Equation.Atom.mk l .e0
  if l = s.init then ⟨lhs, .empty⟩
  else ⟨lhs, inters ((s.flow.filter (fun (_, ll) => l == ll)).map (fun (l', _l) => .var (Equation.Atom.mk l' .e1)))⟩

def exit (s : Stmt) (l : Label) : Equation Value :=
  let lhs := Equation.Atom.mk l .e1
  let b := s.block! l
  ⟨lhs, .union (.diff (.var ⟨l, .e0⟩) (.lit (.ofList (kill s b)))) (.lit (.ofList (gen b)))⟩

public def equations (s : Stmt) : List (Equation Value) :=
  s.labels.flatMap (fun l => [entry s l, exit s l])

public def init (s : Stmt) (es : List (Equation Value))
  : Std.TreeMap Equation.Atom (Std.TreeSet Value) :=
  let aexp : List Value := s.aexp
  let univ : Std.TreeSet Value := .ofList aexp
  es.foldl (fun acc eq => acc.insert eq.lhs univ) .empty

end AvailableExpression

namespace ReachingDefinition

@[expose] public def Value := Var × Option Label

public instance : Ord Value where
  compare x y :=
    match compare x.fst y.fst with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare x.snd y.snd

public def Value.toString (v : Value) : String :=
  match v.snd with
  | none => s!"({v.fst}, ?)"
  | some l => s!"({v.fst}, {l})"

public instance : ToString Value := ⟨Value.toString⟩

def kill (stmt : Stmt) : Block → List Value
  | .assign x _ _ =>
    ([(x, none)] : List Value) ++ (stmt.blocks.filterMap (isDef x))
  | _ => ∅
  where
    isDef (x : Var) (block : Block) : Option Value :=
      match block with
      | .assign x' _ _ => if x == x' then some (x, some block.label) else none
      | _ => none

def gen : Block → List Value
  | .assign x _ l => [(x, some l)]
  | _ => ∅


def entry (s : Stmt) (l : Label) : Equation Value :=
  let lhs := Equation.Atom.mk l .e0
  let rhs1 : List Value := s.FV.map (fun x => (x, none))
  let rhs2 : List (Equation.Expr Value)
    := s.flow.filterMap (fun (l', l'') => if l'' == l then
      some (.var (.mk l' .e1)) else none)
  if l = s.init then ⟨lhs, .lit (.ofList rhs1)⟩
  else ⟨lhs, unions rhs2⟩

def exit (s : Stmt) (l : Label) : Equation Value :=
  let lhs := Equation.Atom.mk l .e1
  let b := s.block! l
  ⟨lhs, .union (.diff (.var ⟨l, .e0⟩) (.lit (.ofList (kill s b)))) (.lit (.ofList (gen b)))⟩

public def equations (s : Stmt) : List (Equation Value) :=
  s.labels.flatMap (fun l => [entry s l, exit s l])

public def init {α} [Ord α] (es : List (Equation α))
  : Std.TreeMap Equation.Atom (Std.TreeSet α) :=
  es.foldl (fun acc eq => acc.insert eq.lhs .empty) .empty

end ReachingDefinition

namespace VeryBusyExpression

end VeryBusyExpression

namespace LiveVariable

end LiveVariable

end ProgramAnalysis.DataFlowAnalysis
