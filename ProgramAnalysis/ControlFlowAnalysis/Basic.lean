module

public import Std.Data.TreeSet
public import Std.Data.TreeMap

public def Std.TreeSet.subset (s1 s2 : Std.TreeSet α cmp) : Bool :=
  s1.all s2.contains

public def List.update [BEq α] (xs : List (α × β)) (x : α) (y : β) : List (α × β) :=
  match xs with
  | [] => [(x, y)]
  | xy :: xys => if xy.fst == x then (x, y) :: xys else xy :: xys.update x y

namespace ProgramAnalysis.ControlFlowAnalysis

public abbrev Label := Nat

public abbrev Var := String

public abbrev Set α (cmp := by exact compare) := Std.TreeSet α cmp

public abbrev Map α β (cmp := by exact compare) := Std.TreeMap α β cmp

end ProgramAnalysis.ControlFlowAnalysis
