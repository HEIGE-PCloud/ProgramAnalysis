import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis

def matrix1 : Matrix (Fin 2) (Fin 3) Nat := ![![1, 2, 3], ![4, 5, 6]]
def matrix2 : Matrix (Fin 3) (Fin 2) Nat := ![![1, 2], ![3, 4], ![5, 6]]

#eval matrix1
#eval matrix1 * matrix2


def matrix3 : Matrix (Fin 11) (Fin 11) Nat := 0

def manualBasisMatrix (row col : Fin 3) : Matrix (Fin 3) (Fin 3) Nat :=
  fun i j => if i = row ∧ j = col then 1 else 0
