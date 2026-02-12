module

public import ProgramAnalysis.DataFlowAnalysis.While
public import Batteries.Data.List
public import Std.Data.TreeSet
public import Std.Data.TreeMap


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
deriving BEq, Repr, Ord

def EquationType.pp (e : EquationType) : String :=
  match e with
    | entry => "entry"
    | exit => "exit"

public structure EquationAtom where
  label : Label
  ty : EquationType
deriving BEq, Repr, Ord

def EquationAtom.pp (e : EquationAtom) : String := s!"AE {e.ty.pp} ({e.label})"

public inductive SetExpr where
  | empty : SetExpr
  | var : EquationAtom → SetExpr
  | lit : Std.TreeSet AExp → SetExpr
  | union : SetExpr → SetExpr → SetExpr
  | inter : SetExpr → SetExpr → SetExpr
  | diff : SetExpr → SetExpr → SetExpr
deriving Repr

public def inters : List SetExpr → SetExpr
  | [] => .empty
  | x :: xs => .inter x (inters xs)

public structure Equation where
  lhs : EquationAtom
  rhs : SetExpr
deriving Repr

public def Equation.build (s : Stmt) (l : Label) (ty : EquationType) : Equation :=
  let lhs := EquationAtom.mk l ty
  let b := s.block! l
  match ty with
    | .entry => if l = s.init then
      ⟨lhs, .empty⟩
    else
      ⟨lhs, inters (s.flow.map (fun (_l, l') => .var (EquationAtom.mk l' .exit)))⟩
    | .exit => ⟨lhs, .union (.diff (.var ⟨l, .entry⟩) (.lit (.ofList (kill s b)))) (.lit (.ofList (gen s b)))⟩

public def Equation.buildAll (s : Stmt) : List Equation :=
  s.labels.flatMap (fun l => [Equation.build s l .entry, Equation.build s l .exit])

public def chaoticInit (es : List Equation) : Std.TreeMap EquationAtom (Std.TreeSet AExp) :=
  es.foldl (fun acc eq => acc.insert eq.lhs .empty) .empty


def SetExpr.eval (e : SetExpr) (env : Std.TreeMap EquationAtom (Std.TreeSet AExp))  : Std.TreeSet AExp :=
  match e with
  | .empty => ∅
  | .var atom => env.getD atom ∅
  | .lit s => s
  | .union a b => (a.eval env) ∪ (b.eval env)
  | .inter a b => (a.eval env) ∩ (b.eval env)
  | .diff a b => (a.eval env) \ (b.eval env)

public def chaoticIter
  (env : Std.TreeMap EquationAtom (Std.TreeSet AExp))
  (es : List Equation)
  : Std.TreeMap EquationAtom (Std.TreeSet AExp) :=
  es.foldl (fun acc eq => acc.insert eq.lhs (eq.rhs.eval env)) env

partial def chaoticIters' (es : List Equation) (env : Std.TreeMap EquationAtom (Std.TreeSet AExp)) :=
  let env' := chaoticIter env es
  if env' == env then env
  else chaoticIters' es env'

public def chaoticIters (es : List Equation) :=
  chaoticIters' es (chaoticInit es)

end AvailableExpression

end ProgramAnalysis.DataFlowAnalysis
