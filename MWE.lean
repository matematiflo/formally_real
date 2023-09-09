import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.BigOperators.Lemmas

def sum_of_list_div {F : Type} [Semifield F] 
  (L : List F) (c : F) : (L.map (. / c)).sum = (1 / c) * L.sum 
    := by simp [div_eq_mul_inv, List.sum_map_mul_right, mul_comm]
