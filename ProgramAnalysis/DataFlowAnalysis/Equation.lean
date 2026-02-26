module
public import Std.Data.TreeSet
public import ProgramAnalysis.DataFlowAnalysis.While

namespace ProgramAnalysis.DataFlowAnalysis

public inductive Equation.AtomType
  | e0
  | e1
deriving BEq, Repr, Ord

public def Equation.AtomType.toString : Equation.AtomType → String
  | e0 => "∘"
  | e1 => "·"

public instance : ToString Equation.AtomType := ⟨Equation.AtomType.toString⟩

public structure Equation.Atom where
  label : While.Label
  ty : Equation.AtomType
deriving BEq, Repr, Ord

public def Equation.Atom.toString (e : Equation.Atom) : String :=
  s!"Analysis{e.ty}({e.label})"

public instance : ToString Equation.Atom := ⟨Equation.Atom.toString⟩

public inductive Equation.Expr  where
  | empty : Equation.Expr
  | var : Equation.Atom → Equation.Expr
  | lit : Std.TreeSet While.AExp → Equation.Expr
  | union : Equation.Expr → Equation.Expr → Equation.Expr
  | inter : Equation.Expr → Equation.Expr → Equation.Expr
  | diff : Equation.Expr → Equation.Expr → Equation.Expr
deriving Repr

public def Equation.Expr.toString : Equation.Expr → String
  | .empty => "∅"
  | .var atom => atom.toString
  | .lit s =>
    let elems := String.intercalate ", " (s.toList.map (fun a => a.toString))
    "{" ++ elems ++ "}"
  | .union a b => s!"({a.toString} ∪ {b.toString})"
  | .inter a b => s!"({a.toString} ∩ {b.toString})"
  | .diff a b => s!"({a.toString} \\ {b.toString})"

public instance : ToString Equation.Expr := ⟨Equation.Expr.toString⟩

public def inters : List Equation.Expr → Equation.Expr
  | [] => .empty
  | x :: [] => x
  | x :: xs => .inter x (inters xs)

public structure Equation where
  lhs : Equation.Atom
  rhs : Equation.Expr
deriving Repr

public def Equation.toString : Equation → String
  | ⟨lhs, rhs⟩ => s!"{lhs.toString} = {rhs.toString}"

public instance : ToString Equation := ⟨Equation.toString⟩

public def chaoticIterationInit (es : List Equation)
  : Std.TreeMap Equation.Atom (Std.TreeSet While.AExp) :=
  es.foldl (fun acc eq => acc.insert eq.lhs .empty) .empty

def Equation.Expr.eval
  (env : Std.TreeMap Equation.Atom (Std.TreeSet While.AExp))
  : Equation.Expr → Std.TreeSet While.AExp
  | .empty => ∅
  | .var atom => env.getD atom ∅
  | .lit s => s
  | .union a b => (a.eval env) ∪ (b.eval env)
  | .inter a b => (a.eval env) ∩ (b.eval env)
  | .diff a b => (a.eval env) \ (b.eval env)

def chaoticIterationOnce
  (env : Std.TreeMap Equation.Atom (Std.TreeSet While.AExp))
  (es : List Equation)
  : Std.TreeMap Equation.Atom (Std.TreeSet While.AExp) :=
  es.foldl (fun acc eq => acc.insert eq.lhs (eq.rhs.eval env)) env

-- TODO: Prove termination?
partial def chaoticIteration'
  (es : List Equation)
  (env : Std.TreeMap Equation.Atom (Std.TreeSet While.AExp)) :=
  let env' := chaoticIterationOnce env es
  if env' == env then env
  else chaoticIteration' es env'

public def chaoticIteration (es : List Equation) :=
  chaoticIteration' es (chaoticIterationInit es)

end ProgramAnalysis.DataFlowAnalysis
