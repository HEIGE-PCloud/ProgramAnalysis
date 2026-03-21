import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker

def matrix1 : Matrix (Fin 2) (Fin 3) Nat := ![![1, 2, 3], ![4, 5, 6]]
def matrix2 : Matrix (Fin 3) (Fin 2) Nat := ![![1, 2], ![3, 4], ![5, 6]]

#eval matrix1
#eval matrix1 * matrix2

def matrix3 : Matrix (Fin 11) (Fin 11) Nat := 0

def A : Matrix (Fin 2) (Fin 2) Nat :=
  ![![1, 2],
    ![3, 4]]

-- Let's define a simple 2x2 matrix B
def B : Matrix (Fin 2) (Fin 2) Nat :=
  ![![0, 5],
    ![6, 0]]

open Kronecker in
def tensorProduct {m n k j : Nat}
  (A : Matrix (Fin m) (Fin n) Nat)
  (B : Matrix (Fin k) (Fin j) Nat) :
  Matrix (Fin (m * k)) (Fin (n * j)) Nat :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)

infixl:70 " ⊗ " => tensorProduct

private def padLeft (width : Nat) (s : String) : String :=
  String.ofList (List.replicate (width - s.length) ' ') ++ s

def Matrix.prettyPrint [ToString α] {m n : Nat} (M : Matrix (Fin m) (Fin n) α) : String :=
  let cells : Array (Array String) :=
    Array.ofFn fun i : Fin m => Array.ofFn fun j : Fin n => toString (M i j)
  let colWidths : Array Nat :=
    Array.ofFn fun j : Fin n =>
      cells.foldl (fun w row => max w row[j.val]!.length) 0
  let rows : Array String :=
    cells.map fun row =>
      "| " ++ String.intercalate "  " (Array.zipWith (fun s w => padLeft w s) row colWidths).toList ++ " |"
  String.intercalate "\n" rows.toList

instance [ToString α] {m n : Nat} : ToString (Matrix (Fin m) (Fin n) α) :=
  ⟨Matrix.prettyPrint⟩

#eval IO.println (toString (A ⊗ B))
