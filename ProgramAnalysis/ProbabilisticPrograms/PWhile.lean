module
public import Lean

namespace ProgramAnalysis.ProbabilisticPrograms

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

public instance : ToString Op_a := ⟨Op_a.toString⟩

public inductive Op_b
  | and
  | or
deriving Repr, Ord, DecidableEq

public def Op_b.toString : Op_b → String
  | .and => "∧"
  | .or => "∨"

public instance : ToString Op_b := ⟨Op_b.toString⟩

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

public instance : ToString Op_r := ⟨Op_r.toString⟩

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

public instance : ToString BoolAtom := ⟨BoolAtom.toString⟩

public inductive Stmt
  | stop : Label → Stmt
  | skip : Label → Stmt
  | assign : Var → ArithAtom → Label → Stmt
  | assign? : Var → List ArithAtom → Label → Stmt
  | seq : Stmt → Stmt → Stmt
  | choose : Nat → Stmt → Nat → Stmt → Stmt
  | sif : BoolAtom → Label → Stmt → Stmt → Stmt
  | swhile : BoolAtom → Label → Stmt → Stmt
deriving Repr, Ord, DecidableEq

public def Stmt.toString : Stmt → String
  | .stop l => s!"[stop]{l.toSuperscriptString}"
  | .skip l => s!"[skip]{l.toSuperscriptString}"
  | .assign var arith l => s!"[{var} := {arith}]{l.toSuperscriptString}"
  | .assign? var ariths l => s!"[{var} ?= {ariths}]{l.toSuperscriptString}"
  | .seq s1 s2 => s!"{s1.toString}\n{s2.toString}"
  | .choose p1 s1 p2 s2 => s!"choose {p1}:{s1.toString} or {p2}:{s2.toString} ro"
  | .sif b l s1 s2 => s!"if [{b}]{l.toSuperscriptString} then {s1.toString} else {s2.toString} fi"
  | .swhile b l s => s!"while [{b}]{l.toSuperscriptString} do {s.toString} od"

instance : ToString Stmt := ⟨Stmt.toString⟩

open Lean Elab Meta

declare_syntax_cat pwhile_op_a
scoped syntax "+" : pwhile_op_a
scoped syntax "-" : pwhile_op_a
scoped syntax "*" : pwhile_op_a
scoped syntax "/" : pwhile_op_a

declare_syntax_cat pwhile_op_b
scoped syntax "&&" : pwhile_op_b
scoped syntax "||" : pwhile_op_b

declare_syntax_cat pwhile_op_r
scoped syntax "==" : pwhile_op_r
scoped syntax "!=" : pwhile_op_r
scoped syntax "<" : pwhile_op_r
scoped syntax "<=" : pwhile_op_r
scoped syntax ">" : pwhile_op_r
scoped syntax ">=" : pwhile_op_r

declare_syntax_cat pwhile_arith_atom
scoped syntax ident : pwhile_arith_atom
scoped syntax num : pwhile_arith_atom
scoped syntax "-" num : pwhile_arith_atom
scoped syntax pwhile_arith_atom pwhile_op_a pwhile_arith_atom : pwhile_arith_atom
scoped syntax "(" pwhile_arith_atom ")" : pwhile_arith_atom

declare_syntax_cat pwhile_bool_atom
scoped syntax "true" : pwhile_bool_atom
scoped syntax "false" : pwhile_bool_atom
scoped syntax "not" pwhile_bool_atom : pwhile_bool_atom
scoped syntax pwhile_bool_atom pwhile_op_b pwhile_bool_atom : pwhile_bool_atom
scoped syntax pwhile_arith_atom pwhile_op_r pwhile_arith_atom : pwhile_bool_atom
scoped syntax "(" pwhile_bool_atom ")" : pwhile_bool_atom

declare_syntax_cat pwhile_stmt
scoped syntax "stop" : pwhile_stmt
scoped syntax "skip" : pwhile_stmt
scoped syntax ident ":=" pwhile_arith_atom : pwhile_stmt
scoped syntax ident "?=" pwhile_arith_atom : pwhile_stmt
scoped syntax pwhile_stmt ";" pwhile_stmt : pwhile_stmt
scoped syntax "choose" num ":" pwhile_stmt "or" num ":" pwhile_stmt "ro": pwhile_stmt
scoped syntax "if" pwhile_bool_atom "then" pwhile_stmt "else" pwhile_stmt "fi" : pwhile_stmt
scoped syntax "while" pwhile_bool_atom "do" "(" pwhile_stmt ")" "od" : pwhile_stmt
scoped syntax "(" pwhile_stmt ")" : pwhile_stmt

end ProgramAnalysis.ProbabilisticPrograms
