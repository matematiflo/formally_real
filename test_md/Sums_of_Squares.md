```lean
import Mathlib.Tactic
```

# Sums of squares

We introduce sums of squares and prove some of their basic properties.

The basic setup is that of a general semiring `R`. For example, sums of squares of natural numbers.

For later results, we specialize to rings or fields.

Sums of squares are defined inductively. The definition is computable.

```lean
def sum_of_squares {R : Type} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)

#eval sum_of_squares [1, -2, 3]
#eval sum_of_squares ([] : List ℕ)

example : sum_of_squares [1, -2, 3] = 14 := rfl
```

The sum of squares of the list `L1 ++ L2` is the sum of squares of `L1` plus the sum of squares of `L2`.

```lean
@[simp] 
theorem sum_of_squares_concat {R : Type} [Semiring R] (L1 L2 : List R) : 
  sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
  := by
    induction L1 with
    | nil => simp [sum_of_squares] -- [] ++ L2 = L2 so everything follows by definition of sum_of_squares
    | cons a L ih => 
      simp [sum_of_squares] -- sum_of_squares (a :: (L ++ L2)) = a^2 + sum_of_squares (L ++ L2)
      rw [ih] -- ih : sum_of_squares (L ++ L2) = sum_of_squares L + sum_of_squares L2
      rw [add_assoc] 
    done
```

A sum of squares is invariant under permutations.

```lean
@[simp] 
theorem sum_of_squares_permut {R : Type} [Semiring R] (L1 L2 : List R) : 
  L1 ~ L2 -> sum_of_squares L1 = sum_of_squares L2 
  := by
    intro H
    induction H
    · case nil => rfl -- case when L1 L2 are both empty
    · case cons x l1 l2 Hl Sum12 => -- case when L1 = (x :: l1) and L2 = (x :: l2) with l1 ~ l2
      simp [sum_of_squares] -- by definition, sum_of_squares (x :: lj) = x^2 + sum_of_squares lj
      rw [Sum12] -- by induction, sum_of_squares l1 = sum_of_squares l2
    · case swap x y L => -- case when L1 = (y :: (x :: L)) and L2 = (x :: (y :: L))
      simp [sum_of_squares] -- by definition, sum_of_squares (y :: (x :: L)) = y^2 + (x^2 + sum_of_squares L)
      rw [← add_assoc, ← add_assoc, add_comm (y^2) (x^2)] -- the two expressions are equal in R
    · case trans l1 L l2 H1 H2 Sum1 Sum2 => -- case when L1 ~ L and L ~ L2
      rw [Sum1, Sum2]
    done
```
