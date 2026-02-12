module

public import ProgramAnalysis.DataFlowAnalysis.While

namespace ProgramAnalysis.DataFlowAnalysis

namespace AvailableExpression
open While

def kill : Block → ReaderM Stmt (List AExp)
  | .assign x _ _ => do
    let stmt ← read
    let aexps := stmt.aexp
    pure (aexps.filter (fun a' => a'.FV.elem x))
  | .skip _ => pure ∅
  | .test _ _ => pure ∅

def gen : Block → ReaderM Stmt (List AExp)
  | .assign x a _ => pure (a.aexp.filter (fun a' => !(a'.FV.elem x)))
  | .skip _ => pure []
  | .test b _ => pure b.aexp

def entry (l : Label) : ReaderM Stmt (List AExp) := do
  let stmt ← read
  pure [] -- TODO
  -- if l == stmt.init then pure []
  -- else [].to

def exit (l : Label) : ReaderM Stmt (List AExp) := sorry

end AvailableExpression


end ProgramAnalysis.DataFlowAnalysis
