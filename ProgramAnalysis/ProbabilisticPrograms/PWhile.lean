module

namespace ProgramAnalysis.DataFlowAnalysis.PWhile

public abbrev Var := String

public abbrev Label := Nat

public inductive Op_a
  | plus
  | minus
  | times
  | div
deriving Repr, Ord, DecidableEq

def Op_a.pp : Op_a → String
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .div => "/"

public inductive Op_b
  | and
  | or
deriving Repr, Ord, DecidableEq

def Op_b.pp : Op_b → String
  | .and => "∧"
  | .or => "∨"

public inductive Op_r
  | eq
  | lt
  | gt
  | le
  | ge
  | neq
deriving Repr, Ord, DecidableEq

def Op_r.pp : Op_r → String
  | .eq => "="
  | .lt => "<"
  | .gt => ">"
  | .le => "≤"
  | .ge => "≥"
  | .neq => "≠"

public inductive ArithAtom
  | var : Var → ArithAtom
  | const : Nat → ArithAtom
  | op : Op_a → ArithAtom → ArithAtom → ArithAtom
deriving Repr, Ord, DecidableEq

def ArithAtom.pp : ArithAtom → String
  | .var x => x
  | .const n => toString n
  | .op o a1 a2 => s!"({a1.pp} {o.pp} {a2.pp})"

public inductive BoolAtom
  | btrue : BoolAtom
  | bfalse : BoolAtom
  | not : BoolAtom → BoolAtom
  | op : Op_b → BoolAtom → BoolAtom → BoolAtom
  | rel : Op_r → ArithAtom → ArithAtom → BoolAtom
deriving Repr, Ord, DecidableEq

def BoolAtom.pp : BoolAtom → String
  | .btrue => "true"
  | .bfalse => "false"
  | .not b => s!"(¬{b.pp})"
  | .op o b1 b2 => s!"({b1.pp} {o.pp} {b2.pp})"
  | .rel o a1 a2 => s!"({a1.pp} {o.pp} {a2.pp})"

public inductive Stmt
  | stop : Label → Stmt
  | skip : Label → Stmt
  | assign : Var → ArithAtom → Label → Stmt
  | assign? : Var → List ArithAtom → Label → Stmt -- probabilistic assignment
  | seq : Stmt → Stmt → Stmt
  | choose : Stmt → Stmt → Stmt -- probabilistic choice
  | sif : BoolAtom → Label → Stmt → Stmt → Stmt
  | swhile : BoolAtom → Label → Stmt → Stmt
deriving Repr, Ord, DecidableEq

end ProgramAnalysis.DataFlowAnalysis.PWhile
