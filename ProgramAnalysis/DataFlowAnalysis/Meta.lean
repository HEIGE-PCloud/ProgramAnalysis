module

public import Lean
public import ProgramAnalysis.DataFlowAnalysis.While

namespace ProgramAnalysis.ControlFlowAnalysis.While.Meta

open Lean Elab Meta ProgramAnalysis.DataFlowAnalysis.While

declare_syntax_cat while_op_a
syntax "+" : while_op_a
syntax "-" : while_op_a
syntax "*" : while_op_a
syntax "/" : while_op_a

declare_syntax_cat while_op_b
syntax "&&" : while_op_b
syntax "||" : while_op_b

declare_syntax_cat while_op_r
syntax "==" : while_op_r
syntax "!=" : while_op_r
syntax "<" : while_op_r
syntax "<=" : while_op_r
syntax ">" : while_op_r
syntax ">=" : while_op_r

declare_syntax_cat while_arith_atom
syntax ident : while_arith_atom
syntax num : while_arith_atom
syntax while_arith_atom while_op_a while_arith_atom : while_arith_atom

declare_syntax_cat while_bool_atom
syntax "true" : while_bool_atom
syntax "false" : while_bool_atom
syntax "not" while_bool_atom : while_bool_atom
syntax while_bool_atom while_op_b while_bool_atom : while_bool_atom
syntax while_arith_atom while_op_r while_arith_atom : while_bool_atom

declare_syntax_cat while_stmt
syntax ident ":=" while_arith_atom : while_stmt
syntax "skip" : while_stmt
syntax while_stmt ";" while_stmt : while_stmt
syntax "if" while_bool_atom "then" while_stmt "else" while_stmt : while_stmt
syntax "while" while_bool_atom "do" while_stmt : while_stmt


end ProgramAnalysis.ControlFlowAnalysis.While.Meta
