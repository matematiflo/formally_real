import Init.Data.List.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic

def sum_of_squares {R : Type _} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)
    
@[simp] 
def sum_of_squares_concat {R : Type _} [Semiring R] (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 := 
by
  induction' L1 with a L ih
  · simp [sum_of_squares]
  · simp [sum_of_squares, ih, add_assoc]

-- NEXT: sum_of_squares_erase and sum_of_square_permut ?


