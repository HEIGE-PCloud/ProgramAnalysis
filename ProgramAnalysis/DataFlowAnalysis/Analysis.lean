module

public import ProgramAnalysis.DataFlowAnalysis.While
public import Batteries.Data.List
public import Std.Data.TreeSet
public import Std.Data.TreeMap
public import ProgramAnalysis.DataFlowAnalysis.Equation

namespace ProgramAnalysis.DataFlowAnalysis

open While

public structure Analysis where
  value : Type
  ordValue : Ord value
  toStringValue : ToString value
  name : String
  join : Equation.Expr value → Equation.Expr value → Equation.Expr value
  bottom : Stmt → List value
  extremeValue : Stmt → List value
  extremeLabel : Stmt → List Label
  flow : Stmt → List (Label × Label)
  kill : Stmt → Block → List value
  gen : Stmt → Block → List value

public instance (a : Analysis) : Ord a.value := a.ordValue

public instance (a : Analysis) : ToString a.value := a.toStringValue

def Analysis.e0 (a : Analysis) (s : Stmt) (l : Label) : Equation a.value :=
  let lhs := Equation.Atom.mk l .e0
  let extremeLabel := a.extremeLabel s
  let extremeValue := a.extremeValue s
  let flow := a.flow s
  let as := flow.filterMap (fun (l', ll) => if l == ll then some (Equation.Expr.var (.mk l' .e1)) else none)
  if extremeLabel.elem l then ⟨lhs, .lit (.ofList extremeValue)⟩
  else ⟨lhs, (foldExpr a.join as)⟩

def Analysis.e1 (a : Analysis) (s : Stmt) (l : Label) : Equation a.value :=
  let lhs := Equation.Atom.mk l .e1
  let b := s.block! l
  ⟨lhs, (.union (.diff (.var ⟨l, .e0⟩) (.lit (.ofList (a.kill s b)))) (.lit (.ofList (a.gen s b))))⟩

public def Analysis.equations (a : Analysis) (s : Stmt) : List (Equation a.value) :=
  s.labels.flatMap (fun l => [a.e0 s l, a.e1 s l])

public def Analysis.init (a : Analysis) (s : Stmt) (es : List (Equation a.value))
  : Std.TreeMap Equation.Atom (Std.TreeSet a.value) :=
  let bottom := a.bottom s
  es.foldl (fun acc eq =>
    acc.insert eq.lhs (.ofList bottom)
  ) .empty

namespace AvailableExpression

@[expose] public def Value := AExp
  deriving Ord, ToString

def kill (stmt : Stmt) : Block → List Value
  | .assign x _ _ => stmt.aexp.filter (fun a' => a'.FV.elem x)
  | _ => ∅

def gen (_ : Stmt) : Block → List Value
  | .assign x a _ => a.aexp.filter (fun a' => !(a'.FV.elem x))
  | _ => ∅

public def analysis : Analysis :=
  { value := Value
  , ordValue := inferInstance
  , toStringValue := inferInstance
  , name := "Available Expression"
  , join := .inter
  , bottom := fun s => s.aexp
  , extremeValue := fun _ => []
  , extremeLabel := fun s => [s.init]
  , flow := fun s => s.flow
  , kill := kill
  , gen := gen
  }

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

def gen (_ : Stmt) : Block → List Value
  | .assign x _ l => [(x, some l)]
  | _ => ∅

public def analysis : Analysis :=
  { value := Value
  , ordValue := inferInstance
  , toStringValue := inferInstance
  , name := "Reaching Definition"
  , join := .union
  , bottom := fun _ => []
  , extremeValue := fun s => s.FV.map (fun x => (x, none))
  , extremeLabel := fun s => [s.init]
  , flow := fun s => s.flow
  , kill := kill
  , gen := gen
  }

end ReachingDefinition

namespace VeryBusyExpression

@[expose] public def Value := AExp
  deriving Ord, ToString

def kill (stmt : Stmt) : Block → List Value
  | .assign x _ _ => stmt.aexp.filter (fun a' => a'.FV.elem x)
  | _ => ∅

def gen (_ : Stmt) : Block → List Value
  | .assign _ a _ => a.aexp
  | .test b _ => b.aexp
  | _ => ∅

public def analysis : Analysis :=
  { value := Value
  , ordValue := inferInstance
  , toStringValue := inferInstance
  , name := "Very Busy Expression"
  , join := .inter
  , bottom := fun s => s.aexp
  , extremeValue := fun _ => []
  , extremeLabel := fun s => s.final
  , flow := fun s => s.flowR
  , kill := kill
  , gen := gen
   }

end VeryBusyExpression

namespace LiveVariable

@[expose] public def Value := Var
  deriving Ord, ToString

def kill (_ : Stmt) : Block → List Value
  | .assign x _ _ => [x]
  | _ => ∅

def gen (_ : Stmt) : Block → List Value
  | .assign _ a _ => a.FV
  | .test b _ => b.FV
  | _ => ∅

public def analysis : Analysis :=
  { value := Value
  , ordValue := inferInstance
  , toStringValue := inferInstance
  , name := "Live Variable"
  , join := .union
  , bottom := fun _ => []
  , extremeValue := fun _ => []
  , extremeLabel := fun s => s.final
  , flow := fun s => s.flowR
  , kill := kill
  , gen := gen
   }

end LiveVariable

namespace Test

abbrev Value := Std.TreeSet AExp

def kill (stmt : Stmt) : Block → Value
  | .assign x _ _ => .ofList (stmt.aexp.filter (fun a' => a'.FV.elem x))
  | _ => ∅

def gen (_ : Stmt) : Block → Value
  | .assign x a _ => .ofList (a.aexp.filter (fun a' => !(a'.FV.elem x)))
  | _ => ∅

def f (stmt : Stmt) (l : Label) (v : Value) : Value :=
  (v \ kill stmt B) ∪ gen stmt B
  where B := stmt.block! l

def flow (stmt : Stmt) := stmt.flow

def extremeLabel (stmt : Stmt) : Std.TreeSet Label := {stmt.init}

def extremeValue (_ : Stmt) : Value := ∅

def bot (stmt : Stmt) : Value := .ofList stmt.aexp

def join : Value → Value → Value := .inter

public def subset (s1 s2 : Std.TreeSet α cmp) : Bool :=
  s1.all s2.contains

def leq (v1 : Value) (v2 : Value) : Bool := subset v2 v1

structure MonotoneFramework where
  value : Type
  leq : value → value → Bool
  join : value → value → value
  bot : Stmt → value
  extremeValue : Stmt → value
  extremeLabel : Stmt → Std.TreeSet Label
  flow : Stmt → List (Label × Label)
  transfer : Stmt → Label → value → value

def AE : MonotoneFramework := {
  value := Value
  leq := leq
  join := join
  bot := bot
  extremeValue := extremeValue
  extremeLabel := extremeLabel
  flow := flow
  transfer := f
}
public inductive Equation.AtomType
  | e0
  | e1
deriving DecidableEq, Repr, Ord

public def Equation.AtomType.toString : Equation.AtomType → String
  | e0 => "◦"
  | e1 => "•"

public instance : ToString Equation.AtomType := ⟨Equation.AtomType.toString⟩

public structure Equation.Atom where
  label : Label
  ty : Equation.AtomType
deriving DecidableEq, Repr, Ord

public inductive Equation.Expr (value : Type) where
  | bot : Equation.Expr value
  | lit : value → Equation.Expr value
  | atom : Equation.Atom → Equation.Expr value
  | join : Equation.Expr value → Equation.Expr value → Equation.Expr value
  | app : (value → value) → Equation.Atom → Equation.Expr value

structure Equation (value : Type) : Type where
  lhs : Equation.Atom
  rhs : Equation.Expr value

public def foldExpr (op : Equation.Expr α → Equation.Expr α → Equation.Expr α) : List (Equation.Expr α) → Equation.Expr α
  | [] => .bot
  | x :: [] => x
  | x :: xs => op x (foldExpr op xs)

def e0 (stmt : Stmt) (l : Label) (m : MonotoneFramework) : Equation m.value :=
  let E := m.extremeLabel stmt
  let ι := m.extremeValue stmt
  let F := m.flow stmt
  let lhs := ⟨l, .e0⟩
  let rhs :=
    if l ∈ E then
      .lit ι
    else
      let as : List (Equation.Expr (m.value)) := F.filterMap (fun (l', ll) =>
        if l == ll then
          some (Equation.Expr.atom ⟨l', .e1⟩)
        else
          none)
      foldExpr .join as
  ⟨lhs, rhs⟩

def e1 (stmt : Stmt) (l : Label) (m : MonotoneFramework) : Equation m.value :=
  let lhs := ⟨l, .e1⟩
  let rhs := .app (m.transfer stmt l) ⟨l, .e0⟩
  ⟨lhs, rhs⟩

def equations (m : MonotoneFramework) (s : Stmt) : List (Equation m.value) :=
  s.labels.flatMap (fun l => [e0 s l m, e1 s l m])

def init (m : MonotoneFramework) (s : Stmt) (es : List (Equation m.value))
  : Std.TreeMap Equation.Atom m.value :=
  let bot := m.bot s
  es.foldl (fun acc eq => acc.insert eq.lhs bot) ∅

end Test
end ProgramAnalysis.DataFlowAnalysis
