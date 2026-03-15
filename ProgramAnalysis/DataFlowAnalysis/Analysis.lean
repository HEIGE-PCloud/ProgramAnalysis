module

public import Std.Data.TreeSet
public import ProgramAnalysis.DataFlowAnalysis.While
public import ProgramAnalysis.DataFlowAnalysis.MonotoneFramework

public def subset [Ord α] (s1 s2 : Std.TreeSet α) : Bool :=
  s1.all s2.contains

public instance [ToString α] [Ord α] : ToString (Std.TreeSet α) where
  toString v := ToString.toString v.toList

namespace ProgramAnalysis.DataFlowAnalysis

public def defaultTransfer [Ord value]
  (kill : Stmt → Block → Std.TreeSet value)
  (gen : Stmt → Block → Std.TreeSet value)
  (stmt : Stmt) (l : Label) (v : Std.TreeSet value)
   : Std.TreeSet value :=
  (v \ kill stmt B) ∪ gen stmt B
  where B := stmt.block! l

namespace AvailableExpression

public abbrev Value := Std.TreeSet AExp


def kill (stmt : Stmt) : Block → Value
  | .assign x _ _ => .ofList (stmt.aexp.filter (fun a' => a'.FV.elem x))
  | _ => ∅

def gen (_ : Stmt) : Block → Value
  | .assign x a _ => .ofList (a.aexp.filter (fun a' => !(a'.FV.elem x)))
  | _ => ∅

public def analysis : MonotoneFramework := {
  value := Value
  beq := inferInstance
  toString := inferInstance
  leq := flip subset
  join := .inter
  bot := fun stmt => .ofList stmt.aexp
  extremeValue := fun _ => ∅
  extremeLabel := fun stmt => {stmt.init}
  flow := Stmt.flow
  transfer := defaultTransfer kill gen
}

end AvailableExpression

namespace ReachingDefinition

public instance : Ord (Var × Option Label) where
  compare x y :=
    match compare x.fst y.fst with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare x.snd y.snd

public abbrev Value := Std.TreeSet (Var × Option Label)

public def Value.toString (v : Var × Option Label) : String :=
  match v.snd with
  | none => s!"({v.fst}, ?)"
  | some l => s!"({v.fst}, {l})"

public instance : ToString (Var × Option Label) := ⟨Value.toString⟩

def kill (stmt : Stmt) : Block → Value
  | .assign x _ _ =>
    .ofList ((x, none) :: (stmt.blocks.filterMap (isDef x)))
  | _ => ∅
  where
    isDef (x : Var) (block : Block) : Option (Var × Option Label) :=
      match block with
      | .assign x' _ _ => if x == x' then some (x, some block.label) else none
      | _ => none

def gen (_ : Stmt) : Block → Value
  | .assign x _ l => {(x, some l)}
  | _ => ∅

def extremeValue (stmt : Stmt) : Value :=
  let vs : List (Var × Option Label) := stmt.FV.map (⟨·, .none⟩)
  .ofList vs

public def analysis : MonotoneFramework :=
  {
    value := Value
    beq := inferInstance
    toString := inferInstance
    leq := subset
    join := .union
    bot := fun _ => ∅
    extremeValue := extremeValue
    extremeLabel := fun stmt => {stmt.init}
    flow := Stmt.flow
    transfer := defaultTransfer kill gen
  }

end ReachingDefinition

namespace VeryBusyExpression

public abbrev Value := Std.TreeSet AExp

def kill (stmt : Stmt) : Block → Value
  | .assign x _ _ => .ofList (stmt.aexp.filter (fun a' => a'.FV.elem x))
  | _ => ∅

def gen (_ : Stmt) : Block → Value
  | .assign _ a _ => .ofList a.aexp
  | .test b _ => .ofList b.aexp
  | _ => ∅

public def analysis : MonotoneFramework :=
  {
    value := Value
    beq := inferInstance
    toString := inferInstance
    leq := flip subset
    join := .inter
    bot := fun stmt => .ofList stmt.aexp
    extremeValue := fun _ => ∅
    extremeLabel := fun stmt => .ofList stmt.final
    flow := Stmt.flowR
    transfer := defaultTransfer kill gen
  }

end VeryBusyExpression

namespace LiveVariable

public abbrev Value := Std.TreeSet Var

def kill (_ : Stmt) : Block → Value
  | .assign x _ _ => {x}
  | _ => ∅

def gen (_ : Stmt) : Block → Value
  | .assign _ a _ => .ofList a.FV
  | .test b _ => .ofList b.FV
  | _ => ∅

public def analysis : MonotoneFramework :=
 {
    value := Value
    beq := inferInstance
    toString := inferInstance
    leq := subset
    join := .union
    bot := fun _ => ∅
    extremeValue := fun _ => ∅
    extremeLabel := fun stmt => .ofList stmt.final
    flow := Stmt.flowR
    transfer := defaultTransfer kill gen
 }

end LiveVariable

end ProgramAnalysis.DataFlowAnalysis
