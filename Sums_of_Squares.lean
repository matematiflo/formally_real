import Mathlib.Tactic
/-!
# Sums of squares

We introduce sums of squares and prove some of their basic properties.

The basic setup is that of a general semiring `R`. For example, we can consider sums of squares of natural numbers.

For some results, we specialize to rings or fields.

## Definition and examples

Sums of squares are defined inductively, on terms of type `List R` where `R` is a semiring (a list is either empty or of the form `a :: L`, where `L`is an already defined list). 
-/

def sum_of_squares {R : Type} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)

/-!
Note that the definition is computable.
-/

#eval sum_of_squares [1, -2, 3] -- 14
#eval sum_of_squares ([] : List ℕ) -- 0

example : sum_of_squares [1, -2, 3] = 14 := rfl -- the two terms are definitionally equal

/-!

## Concatenated lists

The sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.
-/

@[simp]
theorem sum_of_squares_concat {R : Type} [Semiring R] (L1 L2 : List R) : 
  sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
  := by
    induction L1 with -- we prove the result by induction on the list L1 (the list type is an inductive type)
    | nil => -- case when L1 is the empty list
      simp [sum_of_squares] -- [] ++ L2 = L2 so everything follows by definition of sum_of_squares
    | cons a L ih => -- case when L1 = (a :: L)
      simp [sum_of_squares] -- (a :: L) ++ L2 = a :: (L ++ L2) and sum_of_squares (a :: (L ++ L2)) = a^2 + sum_of_squares (L ++ L2)
      rw [ih] -- ih : sum_of_squares (L ++ L2) = sum_of_squares L + sum_of_squares L2
      rw [add_assoc] -- the two terms are now equal up to associativity of addition
    done

/-!
## Permutations of elements in a list

A sum of squares is invariant under permutations: `L1 ~ L2 → sum_of_squares L1 = sum_of_squares L2`.
-/

@[simp]
theorem sum_of_squares_permut {R : Type} [Semiring R] {L1 L2 : List R} (H : L1 ~ L2) : 
  sum_of_squares L1 = sum_of_squares L2 
  := by
    induction H -- we prove the result by induction on ~ (the permutation type is an inductive type: L2 is a permutation of L1 if and only if one of four cases occurs)
    · case nil => -- case when L1 L2 are both empty
      rfl -- equality holds by definition
    · case cons x l1 l2 Hl Sum12 => -- case when L1 = (x :: l1) and L2 = (x :: l2) with l1 ~ l2
      simp [sum_of_squares] -- by definition, sum_of_squares (x :: lj) = x^2 + sum_of_squares lj for j = 1, 2
      rw [Sum12] -- by induction, sum_of_squares l1 = sum_of_squares l2
    · case swap x y L => -- case when L1 = (y :: (x :: L)) and L2 = (x :: (y :: L))
      simp [sum_of_squares] -- by definition, sum_of_squares (y :: (x :: L)) = y^2 + (x^2 + sum_of_squares L)
      rw [← add_assoc, ← add_assoc, add_comm (y^2) (x^2)] -- the two expressions are equal in R
    · case trans l1 L l2 H1 H2 Sum1 Sum2 => -- case when L1 ~ L and L ~ L2
      rw [Sum1, Sum2] -- by induction sum_of_squares L1 = sum_of_squares L and sum_of_squares L = sum_of_squares L2
    done

/-!
## Erasing an element

If a term `a : R` is a member of a list `L : List R`, then we can compute `sum_of_squares L` from `sum_of_squares (List.erase L a) in the following way.
-/

@[simp]
def sum_of_squares_erase {R : Type _} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : 
    sum_of_squares L = a ^ 2 + sum_of_squares (List.erase L a) 
    := by
      have H : L ~ a :: List.erase L a := List.perm_cons_erase h
      rw [sum_of_squares_permut H]
      rfl
      done

-- Next multiply or divide terms in the list...

/-!
## Mathlib versions
-/

@[simp]
theorem sum_of_squares_concat2 {R : Type} [Semiring R] (L1 L2 : List R) : 
  sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
  := by
    induction L1 with
    | nil => simp [sum_of_squares]
    | cons _ _ ih => simp [sum_of_squares, ih, add_assoc]
    done

@[simp]
theorem sum_of_squares_permut2 {R : Type} [Semiring R] {L1 L2 : List R} (H : L1 ~ L2) : 
  sum_of_squares L1 = sum_of_squares L2 
  := by 
    induction H with
    | nil => rfl
    | cons _ _ Sum12 => simp [sum_of_squares, Sum12]
    | swap x y _ => simp [sum_of_squares, ← add_assoc, ← add_assoc, add_comm (y^2) (x^2)]
    | trans _ _ Sum1 Sum2 => rw [Sum1, Sum2]
    done
  
@[simp]
def sum_of_squares_erase2 {R : Type _} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : 
    sum_of_squares L = a ^ 2 + sum_of_squares (List.erase L a) 
    := by
      change sum_of_squares L = sum_of_squares (a :: (List.erase L a))
      rw [sum_of_squares_permut (List.perm_cons_erase h)]
      done
