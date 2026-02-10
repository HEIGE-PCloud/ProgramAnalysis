def Var := String
deriving Repr, ToString

def Char.toSuperScript : Char → Char
  | '0' => '⁰'
  | '1' => '¹'
  | '2' => '²'
  | '3' => '³'
  | '4' => '⁴'
  | '5' => '⁵'
  | '6' => '⁶'
  | '7' => '⁷'
  | '8' => '⁸'
  | '9' => '⁹'
  | c => c

def Nat.toSuperscript (n : Nat) : String := (toString n).map Char.toSuperScript

inductive Op
  | plus
deriving Repr

def Op.print : Op → String
  | .plus => "+"

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

mutual
def Term.print : Term → String
  | .c n => s!"{n}"
  | .x v => s!"{v}"
  | .fn x body => s!"(fn {x} => {body.print})"
  | .app e1 e2 => s!"({e1.print} {e2.print})"
  | .ite cond thn els => s!"(if {cond.print} then {thn.print} else {els.print})"
  | .op o e1 e2 => s!"({e1.print} {o.print} {e2.print})"
  | .letin x e1 e2 => s!"(let {x} = {e1.print} in {e2.print})"

def Expr.print : Expr → String
  | .e t l => s!"{t.print}{l.toSuperscript}"
end

instance : ToString Expr where
  toString := Expr.print

instance : ToString Term where
  toString := Term.print
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

def Expr.mkVar (x : Var) : StateM Nat Expr := do
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
  Expr.mkApp (Expr.mkFn "x" (Expr.mkVar "x")) (Expr.mkFn "y" (Expr.mkVar "y"))

#eval example1

/-- Constraint data type
Constraint is in the form of
lhs subset rhs
{t} subset rhs' => lhs subset rhs
where
rhs is of the form C(l) or r(x)
lhs is of the form C(l), r(x), or {t} and all occurances of t
are of the form fn x => e
-/
inductive AbstractDomain
  | cache : Nat → AbstractDomain
  | env : Var → AbstractDomain
deriving Repr

def AbstractDomain.print : AbstractDomain → String
  | .cache n => s!"C({n})"
  | .env var => s!"r({var})"

/-- A term value that appears in constraints (always of the form `fn x => e`) -/
structure TermValue where
  var : Var
  body : Expr
deriving Repr

def TermValue.print (t : TermValue) : String :=
  s!"fn {t.var} => {t.body}"

inductive Constraint
  /-- `lhs ⊆ rhs` -/
  | subset (lhs rhs : AbstractDomain) : Constraint
  /-- `{t} ⊆ rhs` -/
  | literal (t : TermValue) (rhs : AbstractDomain) : Constraint
  /-- `{t} ⊆ rhs' → lhs ⊆ rhs` -/
  | conditional (t : TermValue) (rhs' : AbstractDomain) (lhs rhs : AbstractDomain) : Constraint
deriving Repr

def Constraint.print : Constraint → String
  | .subset lhs rhs => s!"{lhs.print} ⊆ {rhs.print}"
  | .literal t rhs => s!"{t.print} ⊆ {rhs.print}"
  | .conditional t rhs' lhs rhs => s!"{t.print} ⊆ {rhs'.print} => {lhs.print} ⊆ {rhs.print}"


def genCFAConstraints (allFns : List TermValue) : Expr → List Constraint
  | .e term l => match term with
    | .c _ => []
    | .x x => [.subset (.env x) (.cache l)]
    | .ite t0 t1 t2 =>
      genCFAConstraints allFns t0 ++
      genCFAConstraints allFns t1 ++
      genCFAConstraints allFns t2 ++
      [.subset (.cache t1.label) (.cache l)] ++
      [.subset (.cache t2.label) (.cache l)]
    | .letin x t1 t2 =>
      genCFAConstraints allFns t1 ++
      genCFAConstraints allFns t2 ++
      [.subset (.cache t1.label) (.env x)] ++
      [.subset (.cache t2.label) (.cache l)]
    | .op _ t1 t2 =>
      genCFAConstraints allFns t1 ++
      genCFAConstraints allFns t2
    | .fn x e => [Constraint.literal (TermValue.mk x e) (.cache l)] ++ genCFAConstraints allFns e
    | .app t1 t2 =>
      genCFAConstraints allFns t1 ++
      genCFAConstraints allFns t2 ++
      (allFns.map (fun t => Constraint.conditional t (.cache t1.label) (.cache t2.label) (.env t.var))) ++
      (allFns.map (fun t => Constraint.conditional t (.cache t1.label) (.cache t.body.label) (.cache l)))

def allFns : Expr → List TermValue
| .e term _ => match term with
  | .c _ => []
  | .x _ => []
  | .fn x body => [TermValue.mk x body] ++ allFns body
  | .app t1 t2 => allFns t1 ++ allFns t2
  | .ite t0 t1 t2 => allFns t0 ++ allFns t1 ++ allFns t2
  | .op _ t1 t2 => allFns t1 ++ allFns t2
  | .letin _ t1 t2 => allFns t1 ++ allFns t2

def example2 : Expr := .build <|
  Expr.mkLetIn "f₁" (Expr.mkFn "x₁" (Expr.mkVar "x₁"))
    (Expr.mkLetIn "f₂" (Expr.mkFn "x₂" (Expr.mkVar "x₂"))
    (Expr.mkApp (Expr.mkApp (Expr.mkVar "f₁") (Expr.mkVar "f₂")) (Expr.mkFn "y" (Expr.mkVar "y"))))

#eval example2.print

def example2Fns := allFns example2

#eval example2Fns.map (fun t => t.print)
def example2Constraints := genCFAConstraints example2Fns example2

#eval example2Constraints.map (fun c => c.print)
