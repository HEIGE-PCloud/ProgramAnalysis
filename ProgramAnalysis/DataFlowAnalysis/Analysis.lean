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

namespace ConstantPropagation

public inductive ZT where
  | top : ZT
  | z : Int → ZT
deriving BEq, Inhabited

public def ZT.toString : ZT → String
  | .top => "⊤"
  | z x => ToString.toString x

def ZT.leq : ZT → ZT → Bool
  | _, .top => true
  | .z x, .z y => x = y
  | .top, _ => false

def ZT.join : ZT → ZT → ZT
  | .top, _ => .top
  | _, .top => .top
  | .z x, .z y => if x == y then .z x else .top

public instance : ToString ZT := ⟨ZT.toString⟩

public inductive State where
  | bot : State
  | sigma : Std.TreeMap Var ZT → State
deriving BEq

public def State.toString : State → String
  | .bot => "⊥"
  | .sigma env => ToString.toString env.toList

def State.leq : State → State → Bool
  | .bot, _ => true
  | .sigma σ₁, .sigma σ₂ =>
    σ₁.keys.all (fun x => ZT.leq (σ₁.get! x) (σ₂.get! x))
  | _, .bot => false

def State.join : State → State → State
  | .bot, x => x
  | x, .bot => x
  | .sigma σ₁, .sigma σ₂ =>
    .sigma (σ₁.map (fun x z => ZT.join z (σ₂.get! x)))

public instance : ToString State := ⟨State.toString⟩

def extremeValue (stmt : Stmt) : State :=
  .sigma (.ofList (stmt.FV.map (fun x => (x, ZT.top))))

inductive ZTB where
  | top
  | bot
  | z : Int → ZTB

def ZTB.eval : Op_a → ZTB → ZTB → ZTB
  | _, .top, _ => .top
  | _, _, .top => .top
  | .plus, .z x, .z y => .z (x + y)
  | .minus, .z x, .z y => .z (x - y)
  | .times, .z x, .z y => .z (x * y)
  | .div, .z x, .z y => .z (x / y)
  | _, _, _ => .bot

def ofZT : ZT → ZTB
  | .top => .top
  | .z x => .z x

def ofZTB (z : ZTB) (h : z ≠ ZTB.bot): ZT :=
  match z with
  | .top => .top
  | .z x => .z x

def eval : State → ArithAtom → ZTB
  | .bot, .var _ => .bot
  | .sigma σ, .var x => ofZT (σ.get! x)
  | .bot, .const _ => .bot
  | .sigma _, .const n => .z n
  | σ, .op op a₁ a₂ => ZTB.eval op (eval σ a₁) (eval σ a₂)

lemma ofZT_ne_bot (z : ZT) : ofZT z ≠ ZTB.bot := by
  cases z <;> simp [ofZT]

lemma ZTB_eval_ne_bot {op : Op_a} {v₁ v₂ : ZTB}
    (h₁ : v₁ ≠ ZTB.bot) (h₂ : v₂ ≠ ZTB.bot) : ZTB.eval op v₁ v₂ ≠ ZTB.bot := by
  rcases v₁ with _ | _ | v₁
  · simp [ZTB.eval]
  · exact absurd rfl h₁
  · rcases v₂ with _ | _ | v₂
    · simp [ZTB.eval]
    · exact absurd rfl h₂
    · cases op <;> simp [ZTB.eval]

lemma eval_sigma_ne_bot (env : Std.TreeMap Var ZT) :
    ∀ a : ArithAtom, eval (.sigma env) a ≠ ZTB.bot
  | .var x   => ofZT_ne_bot _
  | .const _ => by simp [eval]
  | .op op a₁ a₂ => by
      simp only [eval]
      exact ZTB_eval_ne_bot (eval_sigma_ne_bot env a₁) (eval_sigma_ne_bot env a₂)

theorem eval_bot (σ : State) (a : ArithAtom) :
    eval σ a = ZTB.bot ↔ σ = State.bot := by
  constructor
  · intro h
    cases σ with
    | bot => rfl
    | sigma env => exact absurd h (eval_sigma_ne_bot env a)
  · rintro rfl
    induction a with
    | var x => simp [eval]
    | const n => simp [eval]
    | op op a₁ a₂ ih₁ ih₂ =>
      simp only [eval, ih₁, ih₂]
      cases op <;> rfl

def transfer (stmt : Stmt) (l : Label) (state : State) :  State :=
  let B := stmt.block! l
  match B with
    | .assign x a _ =>
      match state with
        | s@(.sigma σ) => .sigma (σ.insert x (ofZTB (eval s a) (by grind [eval_bot])))
        | .bot => .bot
    | _ => state

public def analysis : MonotoneFramework :=
  {
    value := State
    beq := inferInstance
    toString := inferInstance
    leq := State.leq
    join := State.join
    bot := fun _ => .bot
    extremeValue := extremeValue
    extremeLabel := fun stmt => {stmt.init}
    flow := Stmt.flow
    transfer := transfer
  }

end ConstantPropagation

end ProgramAnalysis.DataFlowAnalysis
