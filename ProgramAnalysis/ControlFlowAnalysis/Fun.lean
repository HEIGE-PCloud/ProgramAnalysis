module
public import ProgramAnalysis.ControlFlowAnalysis.Basic

/-!
# Fun

Fun is a simple ML-like functional language used to demonstrate control flow
analysis.
-/

/-!
## Syntax of Fun

e ∈ Exp expressions (or labelled terms)
t ∈ Term terms (or unlabelled expressions)

e ::= tˡ
t ::= C | x | fn x => e₀ | e₁ e₂ | if e₁ then e₂ else e₃ | e₁ op e₂ | let x = e₁ in e₂
-/

namespace ProgramAnalysis.ControlFlowAnalysis.Fun

public inductive Op
  | plus
  | minus
  | times
  | div
  | eq
  | lt
  | gt
  | le
  | ge
  | neq
deriving Repr, Ord

public def Op.toString : Op → String
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .div => "/"
  | .eq => "=="
  | .lt => "<"
  | .gt => ">"
  | .le => "<="
  | .ge => ">="
  | .neq => "!="

public instance : ToString Op where
  toString := Op.toString

public section -- See: https://github.com/leanprover/lean4/issues/10067
mutual
public inductive Expr
  | e : Term → Label → Expr
deriving Repr, Ord

public inductive Term
  | c : Int → Term
  | x : Var → Term
  | fn : Var → Expr → Term
  | app : Expr → Expr → Term
  | ite : Expr → Expr → Expr → Term
  | op : Op → Expr → Expr → Term
  | letin : Var → Expr → Expr → Term
deriving Repr, Ord
end
end

public section -- See: https://github.com/leanprover/lean4/issues/10067
mutual
public def Term.toString : Term → String
  | .c n => s!"{n}"
  | .x v => s!"{v}"
  | .fn x body => s!"(fn {x} => {body.toString})"
  | .app e1 e2 => s!"({e1.toString} {e2.toString})"
  | .ite cond thn els => s!"(if {cond.toString} then {thn.toString} else {els.toString})"
  | .op o e1 e2 => s!"({e1.toString} {o.toString} {e2.toString})"
  | .letin x e1 e2 => s!"(let {x} = {e1.toString} in {e2.toString})"

public def Expr.toString : Expr → String
  | .e t l => s!"{t.toString}{l.toSuperscript}"
end
end

public instance : ToString Term where
  toString := Term.toString

public instance : ToString Expr where
  toString := Expr.toString

example : Expr := Expr.e (
  Term.app
    (Expr.e (Term.fn "x" (Expr.e (Term.x "x") 1)) 2)
    (Expr.e (Term.fn "y" (Expr.e (Term.x "y") 3)) 4)
) 5

public def Expr.label : Expr → Label
  | Expr.e _ n => n

def freshLabel : StateM Label Label := do
  let n ← get
  set (n + 1)
  return n

public def Expr.mkConst (n : Int) : StateM Label Expr := do
  let l ← freshLabel
  return Expr.e (Term.c n) l

public def Expr.mkVar (x : Var) : StateM Label Expr := do
  let l ← freshLabel
  return Expr.e (Term.x x) l

public def Expr.mkFn (x : Var) (body : StateM Label Expr) : StateM Label Expr := do
  let b ← body
  let l ← freshLabel
  return Expr.e (Term.fn x b) l

public def Expr.mkApp (e1 e2 : StateM Label Expr) : StateM Label Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.app a b) l

public def Expr.mkIte (cond thn els : StateM Label Expr) : StateM Label Expr := do
  let c ← cond
  let t ← thn
  let e ← els
  let l ← freshLabel
  return Expr.e (Term.ite c t e) l

public def Expr.mkOp (o : Op) (e1 e2 : StateM Label Expr) : StateM Label Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.op o a b) l

public def Expr.mkLetIn (x : Var) (e1 e2 : StateM Label Expr) : StateM Label Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.letin x a b) l

public def Expr.build (m : StateM Label Expr) : Expr :=
  (m.run 1).1

/--
((fn x => x¹)² (fn y => y³)⁴)⁵
-/
example : Expr := .build <|
  Expr.mkApp (Expr.mkFn "x" (Expr.mkVar "x")) (Expr.mkFn "y" (Expr.mkVar "y"))

public section
mutual
structure Env where
  env : List (Var × Value)
deriving Repr

inductive Value
  | vInt : Int → Value
  | vBool : Bool → Value
  | closure : Closure → Value
deriving Repr

structure Closure where
  fn : Var × Expr
  env : Env
deriving Repr
end
end

public def Closure.toString : Closure → String
  | ⟨(x, e), _⟩ => s!"[(fn {x} => {e})]"

public instance : ToString Closure where
  toString := Closure.toString

public def Value.toString : Value → String
  | .vInt n => s!"{n}"
  | .vBool b => s!"{b}"
  | .closure c => s!"{c}"

public instance : ToString Value where
  toString := Value.toString

def Value.getBool : Value → Option Bool
  | .vBool b => .some b
  | _ => .none

def Op.eval (op : Op) (v₁ v₂: Value) : Option Value :=
  match (v₁, op, v₂) with
    | (.vInt x₁, .plus, .vInt x₂) => pure (.vInt (x₁ + x₂))
    | (.vInt x₁, .minus, .vInt x₂) => pure (.vInt (x₁ - x₂))
    | (.vInt x₁, .times, .vInt x₂) => pure (.vInt (x₁ * x₂))
    | (.vInt x₁, .div, .vInt x₂) => pure (.vInt (x₁ / x₂))
    | (.vInt x₁, .eq, .vInt x₂) => pure (.vBool (x₁ == x₂))
    | (.vInt x₁, .neq, .vInt x₂) => pure (.vBool (x₁ != x₂))
    | (.vInt x₁, .lt, .vInt x₂) => pure (.vBool (x₁ < x₂))
    | (.vInt x₁, .le, .vInt x₂) => pure (.vBool (x₁ <= x₂))
    | (.vInt x₁, .gt, .vInt x₂) => pure (.vBool (x₁ > x₂))
    | (.vInt x₁, .ge, .vInt x₂) => pure (.vBool (x₁ >= x₂))
    | _ => .none

public partial def Expr.eval (ρ : Env) (e : Expr) : Option Value :=
  match e with | .e t _ => match t with
    | .c n => pure (.vInt n)
    | .x x => ρ.env.lookup x
    | .fn x t₀ => pure (.closure ⟨⟨x, t₀⟩, ρ⟩)
    | .app t₁ t₂ => do
      let v₁ ← eval ρ t₁
      match v₁ with
        | .closure ⟨(x, e₀), ρ'⟩ => do
          let v₂ ← eval ρ t₂
          eval ⟨ρ'.env.update x v₂⟩ e₀
        | _ => .none
    | .ite t₀ t₁ t₂ => do
      let t ← eval ρ t₀
      let b ← t.getBool
      if b then eval ρ t₁ else eval ρ t₂
    | .op op t₁ t₂ => do
      let v₁ ← eval ρ t₁
      let v₂ ← eval ρ t₂
      op.eval v₁ v₂
    | .letin x t₁ t₂ => do
      let v₁ ← eval ρ t₁
      eval ⟨ρ.env.update x v₁⟩ t₂

example : Option Value := (Expr.build <|
  Expr.mkApp (Expr.mkFn "x" (Expr.mkVar "x")) (Expr.mkFn "y" (Expr.mkVar "y"))).eval ⟨[]⟩

end ProgramAnalysis.ControlFlowAnalysis.Fun
