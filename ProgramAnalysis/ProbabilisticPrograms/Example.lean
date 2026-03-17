import Mathlib.Data.Matrix.Basic

def matrix1 : Matrix (Fin 2) (Fin 3) Nat := ![![1, 2, 3], ![4, 5, 6]]
def matrix2 : Matrix (Fin 3) (Fin 2) Nat := ![![1, 2], ![3, 4], ![5, 6]]

#eval matrix1
#eval matrix1 * matrix2
