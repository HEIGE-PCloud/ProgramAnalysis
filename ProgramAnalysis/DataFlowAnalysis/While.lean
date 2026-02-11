module

public abbrev Var := String

public abbrev Label := Nat

public inductive Op_a
  | plus
  | minus
  | times
  | div
deriving Repr, Ord

public inductive Op_b
  | and
  | or
deriving Repr, Ord

public inductive Op_r
  | eq
  | lt
  | gt
  | le
  | ge
  | neq
deriving Repr, Ord

public inductive ArithAtom
  | var : Var → ArithAtom
  | const : Int → ArithAtom
  | op : Op_a → ArithAtom → ArithAtom → ArithAtom
deriving Repr, Ord

public inductive BoolAtom
  | btrue : BoolAtom
  | bfalse : BoolAtom
  | not : BoolAtom → BoolAtom
  | op : Op_b → BoolAtom → BoolAtom → BoolAtom
  | rel : Op_r → ArithAtom → ArithAtom → BoolAtom
deriving Repr, Ord

public inductive Stmt
  | assign : Var → ArithAtom →  Label → Stmt
  | skip : Label → Stmt
  | seq : Stmt → Stmt → Stmt
  | sif : BoolAtom → Label → Stmt → Stmt → Stmt
  | swhile : BoolAtom → Label → Stmt → Stmt
deriving Repr, Ord

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
