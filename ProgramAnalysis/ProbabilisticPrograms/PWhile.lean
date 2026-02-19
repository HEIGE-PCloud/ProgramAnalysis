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

public def Op_a.toString : Op_a → String
  | .plus => "+"
  | .minus => "-"
  | .times => "*"
  | .div => "/"

public instance : ToString Op_a where
  toString := Op_a.toString

public inductive Op_b
  | and
  | or
deriving Repr, Ord, DecidableEq

public def Op_b.toString : Op_b → String
  | .and => "∧"
  | .or => "∨"

public instance : ToString Op_b where
  toString := Op_b.toString

public inductive Op_r
  | eq
  | lt
  | gt
  | le
  | ge
  | neq
deriving Repr, Ord, DecidableEq

public def Op_r.toString : Op_r → String
  | .eq => "="
  | .lt => "<"
  | .gt => ">"
  | .le => "≤"
  | .ge => "≥"
  | .neq => "≠"

public instance : ToString Op_r where
  toString := Op_r.toString

public inductive ArithAtom
  | var : Var → ArithAtom
  | const : Nat → ArithAtom
  | op : Op_a → ArithAtom → ArithAtom → ArithAtom
deriving Repr, Ord, DecidableEq

public def ArithAtom.toString : ArithAtom → String
  | .var x => x
  | .const n => ToString.toString n
  | .op o a1 a2 => s!"({a1.toString} {o.toString} {a2.toString})"

public instance : ToString ArithAtom where
  toString := ArithAtom.toString

public inductive BoolAtom
  | btrue : BoolAtom
  | bfalse : BoolAtom
  | not : BoolAtom → BoolAtom
  | op : Op_b → BoolAtom → BoolAtom → BoolAtom
  | rel : Op_r → ArithAtom → ArithAtom → BoolAtom
deriving Repr, Ord, DecidableEq

public def BoolAtom.toString : BoolAtom → String
  | .btrue => "true"
  | .bfalse => "false"
  | .not b => s!"(¬{b.toString})"
  | .op o b1 b2 => s!"({b1.toString} {o.toString} {b2.toString})"
  | .rel o a1 a2 => s!"({a1.toString} {o.toString} {a2.toString})"

public instance : ToString BoolAtom where
  toString := BoolAtom.toString

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
