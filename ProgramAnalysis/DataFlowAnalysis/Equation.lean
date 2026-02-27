module
public import Std.Data.TreeSet
public import ProgramAnalysis.DataFlowAnalysis.While

namespace ProgramAnalysis.DataFlowAnalysis

public inductive Equation.AtomType
  | e0
  | e1
deriving BEq, Repr, Ord

public def Equation.AtomType.toString : Equation.AtomType → String
  | e0 => "◦"
  | e1 => "•"

public instance : ToString Equation.AtomType := ⟨Equation.AtomType.toString⟩

public structure Equation.Atom where
  label : While.Label
  ty : Equation.AtomType
deriving BEq, Repr, Ord

public def Equation.Atom.toString (e : Equation.Atom) : String :=
  s!"Analysis{e.ty}({e.label})"

public instance : ToString Equation.Atom := ⟨Equation.Atom.toString⟩

public inductive Equation.Expr (α : Type) [Ord α]  where
  | empty : Equation.Expr α
  | var : Equation.Atom → Equation.Expr α
  | lit : Std.TreeSet α → Equation.Expr α
  | union : Equation.Expr α → Equation.Expr α → Equation.Expr α
  | inter : Equation.Expr α → Equation.Expr α → Equation.Expr α
  | diff : Equation.Expr α → Equation.Expr α → Equation.Expr α
deriving Repr

public def Equation.Expr.toString [Ord α] [ToString α]
  : Equation.Expr α → String
  | .empty => "∅"
  | .var atom => atom.toString
  | .lit s =>
    let elems := String.intercalate ", "
      (s.toList.map (fun a => ToString.toString a))
    "{" ++ elems ++ "}"
  | .union a b => s!"({a.toString} ∪ {b.toString})"
  | .inter a b => s!"({a.toString} ∩ {b.toString})"
  | .diff a b => s!"({a.toString} \\ {b.toString})"

public instance [Ord α] [ToString α] : ToString (Equation.Expr α)
  := ⟨Equation.Expr.toString⟩

public def foldExpr [Ord α] (op : Equation.Expr α → Equation.Expr α → Equation.Expr α) : List (Equation.Expr α) → Equation.Expr α
  | [] => .empty
  | x :: [] => x
  | x :: xs => op x (foldExpr op xs)

public structure Equation (α : Type) [Ord α] where
  lhs : Equation.Atom
  rhs : Equation.Expr α
deriving Repr

public def Equation.toString [Ord α] [ToString α] : Equation α → String
  | ⟨lhs, rhs⟩ => s!"{lhs} = {rhs}"

public instance [Ord α] [ToString α] : ToString (Equation α)
  := ⟨Equation.toString⟩

def Equation.Expr.eval [Ord α]
  (env : Std.TreeMap Equation.Atom (Std.TreeSet α))
  : Equation.Expr α → Std.TreeSet α
  | .empty => ∅
  | .var atom => env.getD atom ∅
  | .lit s => s
  | .union a b => (a.eval env) ∪ (b.eval env)
  | .inter a b => (a.eval env) ∩ (b.eval env)
  | .diff a b => (a.eval env) \ (b.eval env)

def chaoticIterationOnce [Ord α]
  (env : Std.TreeMap Equation.Atom (Std.TreeSet α))
  (es : List (Equation α))
  : Std.TreeMap Equation.Atom (Std.TreeSet α) :=
  es.foldl (fun acc eq => acc.insert eq.lhs (eq.rhs.eval env)) env

-- TODO: Prove termination?
partial def chaoticIteration' [Ord α]
  (es : List (Equation α))
  (env : Std.TreeMap Equation.Atom (Std.TreeSet α)) :=
  let env' := chaoticIterationOnce env es
  if env' == env then env
  else chaoticIteration' es env'

public def chaoticIteration [Ord α]
  (es : List (Equation α))
  (init : List (Equation α) → Std.TreeMap Equation.Atom (Std.TreeSet α))
  : Std.TreeMap Equation.Atom (Std.TreeSet α) :=
  chaoticIteration' es (init es)

end ProgramAnalysis.DataFlowAnalysis
