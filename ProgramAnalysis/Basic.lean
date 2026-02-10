def hello := "world"

def Var := String
deriving Repr

inductive Op
  | plus
deriving Repr

mutual
inductive Expr
  | e : Term → Nat → Expr
deriving Repr

inductive Term
  | c : Nat → Term
  | x : Var → Term
  | fn : Var → Expr → Term
  | app : Expr → Expr → Term
  | ite : Expr → Expr → Expr → Term
  | op : Op → Expr → Expr → Term
  | letin : Var → Expr → Expr → Term
deriving Repr
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

def Expr.mkConst (n : Nat) : StateM Nat Expr := do
  let l ← freshLabel
  return Expr.e (Term.c n) l

def mkVar (x : Var) : StateM Nat Expr := do
  let l ← freshLabel
  return Expr.e (Term.x x) l

def Expr.mkFn (x : Var) (body : StateM Nat Expr) : StateM Nat Expr := do
  let b ← body
  let l ← freshLabel
  return Expr.e (Term.fn x b) l

def Expr.mkApp (e1 e2 : StateM Nat Expr) : StateM Nat Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.app a b) l

def Expr.mkIte (cond thn els : StateM Nat Expr) : StateM Nat Expr := do
  let c ← cond
  let t ← thn
  let e ← els
  let l ← freshLabel
  return Expr.e (Term.ite c t e) l

def Expr.mkOp (o : Op) (e1 e2 : StateM Nat Expr) : StateM Nat Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.op o a b) l

def Expr.mkLetIn (x : Var) (e1 e2 : StateM Nat Expr) : StateM Nat Expr := do
  let a ← e1
  let b ← e2
  let l ← freshLabel
  return Expr.e (Term.letin x a b) l

def Expr.build (m : StateM Nat Expr) : Expr :=
  (m.run 1).1

def example1 : Expr := .build <|
  Expr.mkApp (Expr.mkFn "x" (mkVar "x")) (Expr.mkFn "y" (mkVar "y"))

#eval example1
