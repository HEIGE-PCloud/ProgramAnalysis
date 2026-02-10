def hello := "world"

def Var := String

inductive Op
  | plus

mutual
inductive Expr
  | e : Term → Nat → Expr

inductive Term
  | c : Nat → Term
  | x : Var → Term
  | fn : Var → Expr → Term
  | app : Expr → Expr → Term
  | ite : Expr → Expr → Expr → Term
  | op : Op → Expr → Expr → Term
  | letin : Var → Expr → Expr → Term
end

example : Expr := Expr.e (
  Term.app
    (Expr.e (Term.fn "x" (Expr.e (Term.x "x") 1)) 2)
    (Expr.e (Term.fn "y" (Expr.e (Term.x "y") 3)) 4)
) 5

private def Expr.label : Expr → Nat
  | Expr.e _ n => n

private def freshLabel : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  return n

def mkC (n : Nat) : StateM Nat Expr := do
  let l ← freshLabel
  return Expr.e (Term.c n) l

def mkX (x : Var) : StateM Nat Expr := do
  let l ← freshLabel
  return Expr.e (Term.x x) l

def mkFn (x : Var) (body : StateM Nat Expr) : StateM Nat Expr := do
  let b ← body
  let l ← freshLabel
  return Expr.e (Term.fn x b) l

def mkApp (e1 e2 : StateM Nat Expr) : StateM Nat Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.app a b) l

def mkIte (cond thn els : StateM Nat Expr) : StateM Nat Expr := do
  let c ← cond
  let t ← thn
  let e ← els
  let l ← freshLabel
  return Expr.e (Term.ite c t e) l

def mkOp (o : Op) (e1 e2 : StateM Nat Expr) : StateM Nat Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.op o a b) l

def mkLetIn (x : Var) (e1 e2 : StateM Nat Expr) : StateM Nat Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.letin x a b) l

def buildExpr (m : StateM Nat Expr) : Expr :=
  (m.run 0).1

example : Expr := buildExpr <|
  mkApp (mkFn "x" (mkX "x")) (mkFn "y" (mkX "y"))
