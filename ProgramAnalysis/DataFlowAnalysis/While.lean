module

namespace ProgramAnalysis.DataFlowAnalysis.While

public abbrev Var := String

public abbrev Label := Nat

public inductive Op_a
  | plus
  | minus
  | times
  | div
deriving Repr, Ord, DecidableEq

public inductive Op_b
  | and
  | or
deriving Repr, Ord, DecidableEq

public inductive Op_r
  | eq
  | lt
  | gt
  | le
  | ge
  | neq
deriving Repr, Ord, DecidableEq

public inductive ArithAtom
  | var : Var → ArithAtom
  | const : Nat → ArithAtom
  | op : Op_a → ArithAtom → ArithAtom → ArithAtom
deriving Repr, Ord, DecidableEq

public inductive BoolAtom
  | btrue : BoolAtom
  | bfalse : BoolAtom
  | not : BoolAtom → BoolAtom
  | op : Op_b → BoolAtom → BoolAtom → BoolAtom
  | rel : Op_r → ArithAtom → ArithAtom → BoolAtom
deriving Repr, Ord, DecidableEq

public inductive Stmt
  | assign : Var → ArithAtom → Label → Stmt
  | skip : Label → Stmt
  | seq : Stmt → Stmt → Stmt
  | sif : BoolAtom → Label → Stmt → Stmt → Stmt
  | swhile : BoolAtom → Label → Stmt → Stmt
deriving Repr, Ord, DecidableEq

/--
[y := x]¹;
[z := y]²;
while [y > 1]³ do
  [z := z * y]⁴;
  [y := y - 1]⁵;
[y := 0]⁶
-/
example : Stmt :=
  open Op_a Op_b Op_r ArithAtom BoolAtom Stmt in
  (seq (assign "x" (var "y") 1)
  (seq (assign "y" (var "z") 2)
  (seq (swhile (rel gt (var "y") (const 1)) 3 (seq
    (assign "z" (op times (var "z") (var "y")) 4)
    (assign "y" (op minus (var "y") (const 1)) 5)))
  (Stmt.assign "y" (const 0) 6))))

def freshLabel : StateM Label Label := do
  let n ← get
  set (n + 1)
  return n

public def Stmt.mkAssign (x : Var) (a : ArithAtom) : StateM Label Stmt := do
  let l ← freshLabel
  return Stmt.assign x a l

public def Stmt.mkSkip : StateM Label Stmt := do
  let l ← freshLabel
  return Stmt.skip l

public def Stmt.mkSeq (s1 s2 : StateM Label Stmt) : StateM Label Stmt := do
  let a ← s1
  let b ← s2
  return Stmt.seq a b

public def Stmt.mkIf (b : BoolAtom) (thn els : StateM Label Stmt) : StateM Label Stmt := do
  let l ← freshLabel
  let t ← thn
  let e ← els
  return Stmt.sif b l t e

public def Stmt.mkWhile (b : BoolAtom) (body : StateM Label Stmt) : StateM Label Stmt := do
  let l ← freshLabel
  let s ← body
  return Stmt.swhile b l s

public def Stmt.build (m : StateM Label Stmt) : Stmt :=
  (m.run 1).1

/--
[y := x]¹;
[z := y]²;
while [y > 1]³ do
  [z := z * y]⁴;
  [y := y - 1]⁵;
[y := 0]⁶
-/
example : Stmt := .build <|
  open Op_a Op_r ArithAtom BoolAtom Stmt in
  mkSeq (mkAssign "x" (var "y"))
  (mkSeq (mkAssign "y" (var "z"))
  (mkSeq (mkWhile (rel gt (var "y") (const 1))
    (mkSeq (mkAssign "z" (op times (var "z") (var "y")))
            (mkAssign "y" (op minus (var "y") (const 1)))))
  (mkAssign "y" (const 0))))

@[grind]
public def Stmt.init : Stmt → Label
  | .assign _ _ l => l
  | .skip l => l
  | .seq s _ => s.init
  | .sif _ l _ _ => l
  | .swhile _ l _ => l

@[grind]
public def Stmt.final : Stmt → List Label
  | .assign _ _ l => [l]
  | .skip l => [l]
  | .seq _ s => s.final
  | .sif _ _ s1 s2 => s1.final ++ s2.final
  | .swhile _ l _ => [l]

public inductive Block
  | assign : Var → ArithAtom → Label → Block
  | skip : Label → Block
  | test : BoolAtom → Label → Block
deriving DecidableEq

@[grind]
public def Block.label : Block → Label
  | .assign _ _ l => l
  | .skip l => l
  | .test _ l => l

@[grind]
public def Stmt.blocks : Stmt → List Block
  | .assign x a l => [.assign x a l]
  | .skip l => [.skip l]
  | .seq s1 s2 => s1.blocks ++ s2.blocks
  | .sif b l s1 s2 => [.test b l] ++ s1.blocks ++ s2.blocks
  | .swhile b l s => [.test b l] ++ s.blocks

@[grind]
public def Stmt.labels (s : Stmt) : List Label := s.blocks.map Block.label

@[grind =]
public theorem init_S_in_labels_S : ∀ s : Stmt, s.labels.elem s.init := by
  intro s; induction s <;> grind [Stmt.init, Stmt.labels, Stmt.blocks, Block.label]

@[grind =]
public theorem final_S_in_labels_S : ∀ s : Stmt, ∀ l : Label, s.final.elem l → s.labels.elem l := by
  intro s; induction s <;> grind [Stmt.final, Stmt.labels, Stmt.blocks, Block.label]

@[grind]
public def Stmt.flow : Stmt → List (Label × Label)
  | .assign _ _ _ => []
  | .skip _ => []
  | .seq s1 s2 => s1.flow ++ s2.flow ++ (s1.final.map (·, s2.init))
  | .sif _ l s1 s2 => s1.flow ++ s2.flow ++ [(l, s1.init), (l, s2.init)]
  | .swhile _ l s => s.flow ++ [(l, s.init)] ++ (s.final.map (·, l))

@[grind]
public def Stmt.flowR : Stmt → List (Label × Label) := (.map (fun (x, y) => (y, x))) ∘ Stmt.flow

@[grind]
public def Stmt.labelConsistent (B₁ B₂ : Block) : Prop := B₁.label = B₂.label → B₁ = B₂

end ProgramAnalysis.DataFlowAnalysis.While
