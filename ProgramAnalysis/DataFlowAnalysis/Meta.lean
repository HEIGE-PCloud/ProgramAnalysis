module

public import Lean
public import ProgramAnalysis.DataFlowAnalysis.While

namespace ProgramAnalysis.ControlFlowAnalysis.While.Meta

open Lean Elab Meta ProgramAnalysis.DataFlowAnalysis.While

declare_syntax_cat while_lit
syntax num       : while_lit

meta def elabWhileLit : Syntax → MetaM Expr
  | `(while_lit| $n:num) => mkAppM ``ArithAtom.const  #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

elab "test_elabWhileLit " l:while_lit : term => elabWhileLit l

#reduce test_elabWhileLit 4

end ProgramAnalysis.ControlFlowAnalysis.While.Meta
