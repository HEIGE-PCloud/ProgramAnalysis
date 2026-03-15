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

public def println [Ord α] [ToString α] (solution : Std.TreeMap Equation.Atom (Std.TreeSet α)) : IO Unit :=
  solution.toList.forM (fun (k, v) => IO.println s!"{k} = {v.toList}")

/-!
## The MFP Solution

Input: an instance of a Monotone Framework: (L, 𝓕, F, E, ι, f)
Output: MFP◦, MFP•

Step 1: Initialization of W and Analysis
  W := nil;
  for all (l, l') in F do
    W := cons((l, l'), W);
  for all l in F or E do
    if l in E then Analysis[l] := ι
              else Analysis[l] := ⊥_L;

Step 2: Iteration (updating W and Analysis)
  while W ≠ nil do
    l := fst(head(W)); l' := snd(head(W));
    W := tail(W);
    if fₗ(Analysis[l]) !⊑ Analysis[l'] then
      Analysis[l'] := Analysis[l'] ⊔ fₗ(Analysis[l]);
      for all (l', l'') in F do W := cons((l', l''), W);

Step 3: Presenting the result (MFP◦ and MFP•)
for all l in F or E do
  MFP◦(l) := Analysis[l];
  MFP•(l) := fₗ(Analysis[l])
-/

-- TODO: implementation

end ProgramAnalysis.DataFlowAnalysis
