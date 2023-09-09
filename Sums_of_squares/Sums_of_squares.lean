/-
# Sums of squares

Copyright (c) 2023 Florent Schaffhauser. All rights reserved.  
Released under Apache 2.0 license as described in the file LICENSE.  
Authors: Florent Schaffhauser
-/

import Mathlib.Data.List.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.BigOperators.Lemmas

/-!
We introduce sums of squares and prove some of their basic properties.

The basic setup is that of a general semiring `R`. For example, we can consider sums of squares of natural numbers.

For some results, we specialize to rings or fields.

The notation `ih` in proofs by induction is meant to signify *induction hypothesis*.

## Definition and examples

Sums of squares are defined inductively, on terms of type `List R` where `R` is a semiring (recall that lists are defined inductively themselves: they are either empty or of the form `a :: L`, where `L`is an already defined list). 
-/

def sum_of_squares {R : Type} [Semiring R] : List R → R
  | [] => 0
  | (a :: L) => (a ^ 2) + (sum_of_squares L)

/-!
Note that the definition is computable. In particular, simple equalities can be proved using `rfl`.
-/

#eval sum_of_squares [1, -2, 3] -- 14
#eval sum_of_squares ([] : List ℕ) -- 0

example : sum_of_squares [1, -2, 3] = 14 := rfl -- the two terms are definitionally equal

/-!
## Alternate definition

`sum_of_squares L` can also be computed by squaring the members of the list and summing the resulting list.
-/

def squaring_and_summing {R : Type} [Semiring R] 
  (L : List R) : (L.map (. ^ 2)).sum = sum_of_squares L
    := by
      induction L with -- we prove the result by induction on the list L (the list type is an inductive type)
      | nil => rfl -- case when L is the empty list, the two terms are definitionally equal
      | cons a l ih => simp [sum_of_squares, ih] -- case when L = (a :: l), the two terms reduce to equal ones after some simplifications
      done

/-!
## Concatenated lists

The sum of squares of the list `L1 ++ L2` is equal to the sum of squares of `L1` plus the sum of squares of `L2`.

> `sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2`
-/

@[simp]
def sum_of_squares_concat {R : Type} [Semiring R] 
  (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
    := by
      induction L1 with -- we prove the result by induction on the list L1
      | nil => -- case when L1 is the empty list
        simp [sum_of_squares] -- [] ++ L2 = L2 so everything follows by definition of sum_of_squares
      | cons a L ih => -- case when L1 = (a :: L)
        simp [sum_of_squares] -- (a :: L) ++ L2 = a :: (L ++ L2) and sum_of_squares (a :: (L ++ L2)) = a ^ 2  + sum_of_squares (L ++ L2)
        rw [ih] -- ih : sum_of_squares (L ++ L2) = sum_of_squares L + sum_of_squares L2
        rw [add_assoc] -- the two terms are now equal up to associativity of addition
      done

/-!
## Permuted lists

A sum of squares is invariant under permutations:

> `L1 ~ L2 → sum_of_squares L1 = sum_of_squares L2`.
-/

@[simp]
def sum_of_squares_permut {R : Type} [Semiring R] {L1 L2 : List R} 
  (H : L1 ~ L2) : sum_of_squares L1 = sum_of_squares L2 
    := by
      induction H -- we prove the result by induction on ~ (the permutation type is an inductive type: L2 is a permutation of L1 if and only if one of four cases occurs)
      · case nil => -- case when L1 L2 are both empty
        rfl -- equality holds by definition
      · case cons x l1 l2 Hl Sum12 => -- case when L1 = (x :: l1) and L2 = (x :: l2) with l1 ~ l2
        simp [sum_of_squares] -- by definition, sum_of_squares (x :: lj) = x ^ 2  + sum_of_squares lj for j = 1, 2
        rw [Sum12] -- by induction, sum_of_squares l1 = sum_of_squares l2
      · case swap x y L => -- case when L1 = (y :: (x :: L)) and L2 = (x :: (y :: L))
        simp [sum_of_squares] -- by definition, sum_of_squares (y :: (x :: L)) = y ^ 2  + (x ^ 2  + sum_of_squares L)
        rw [← add_assoc, ← add_assoc, add_comm (y ^ 2) (x ^ 2)] -- the two expressions are equal in R
      · case trans l1 L l2 H1 H2 Sum1 Sum2 => -- case when L1 ~ L and L ~ L2
        rw [Sum1, Sum2] -- by induction sum_of_squares L1 = sum_of_squares L and sum_of_squares L = sum_of_squares L2
      done

/-!
## Erasing a member

If a term `a : R` is a member of a list `L : List R`, then we can compute `sum_of_squares L` from `a` and `sum_of_squares (List.erase L a) in the following way.

In order to be able to use the function `List.erase`, we assume that the semiring `R` has decidable equality.
-/

@[simp]
def sum_of_squares_erase {R : Type} [Semiring R] [DecidableEq R] 
  (L : List R) (a : R) (h : a ∈ L) : sum_of_squares L = a ^ 2 + sum_of_squares (List.erase L a) 
    := by
      change sum_of_squares L = sum_of_squares (a :: (List.erase L a)) -- we can replace the goal with a *definitionally equal* one
      have H : L ~ (a :: (List.erase L a)) := List.perm_cons_erase h -- this is the Mathlib proof that L ~ (a :: (List.erase L a))
      rw [sum_of_squares_permut H] -- since we ha ve a proof that L ~ (a :: (List.erase L a)), we can use the sum_of_squares_permut function that we defined earlier to conclude that the two sums of squares are equal
      done

/-!
## Multiplicative properties

The first result says that if you multiply every member of a list `L : List R` by a constant `c : R`, then the sum of squares of the new list is equal to `c ^ 2 * sum_of_squares L`. 

In order to be able to apply lemmas such as `mul_pow` in the proof, we assume here that the product the semiring `R` is commutative.

We take a look at a few examples first.
-/

#eval sum_of_squares [2 * 1, 2 * ( -2), 2 * 3] -- 56 
#eval 4 * sum_of_squares [1, -2, 3] -- 56

example : sum_of_squares [2 * 1, 2 * ( -2), 2 * 3] = 4 * sum_of_squares [1, -2, 3] := rfl

example (a x y : ℚ) : sum_of_squares [a * x, a * y] = a ^ 2 * sum_of_squares [x, y] 
  := by simp [sum_of_squares, mul_pow, mul_add]
    
@[simp]
def sum_of_squares_of_list_mul {R : Type} [CommSemiring R] 
  (L : List R) (c : R) : sum_of_squares (L.map (c * .)) = c ^ 2 * sum_of_squares L 
    := by
      induction L with -- again an induction on L
      | nil => simp [sum_of_squares] -- the case of the empty list is trivial
      | cons a _ ih => simp [sum_of_squares, ih, mul_add, mul_pow c a 2] -- the case of a list of the form (a :: l) follows from simplifications and the use of the induction hypothesis
      done

@[simp]
def sum_of_squares_of_list_div {F : Type} [Semifield F] 
  (L : List F) (c : F) : sum_of_squares (L.map (. / c)) = (1 / c ^ 2) * sum_of_squares L 
    := by -- this will be an application of sum_of_squares_of_list_mul, using the fact that . / c = . * c⁻¹
      have aux : (fun x => x / c) = (fun x => c⁻¹ * x) 
        := by field_simp
      simp [aux] -- Note that `sum_of_squares_of_list_mul` has been added to `simp`, so we do not need to include it here
      done

/-!
## Golfed versions
-/

def squaring_and_summing_golfed {R : Type} [Semiring R] 
  (L : List R) : (L.map (. ^ 2)).sum = sum_of_squares L
    := by induction L with
      | nil => rfl
      | cons a L ih => simp [sum_of_squares, ih]

@[simp]
theorem sum_of_squares_concat_golfed {R : Type} [Semiring R] 
  (L1 L2 : List R) : sum_of_squares (L1 ++ L2) = sum_of_squares L1 + sum_of_squares L2 
    := by induction L1 with
      | nil => simp [sum_of_squares]
      | cons _ _ ih => simp [sum_of_squares, ih, add_assoc]

@[simp]
theorem sum_of_squares_permut_golfed {R : Type} [Semiring R] {L1 L2 : List R} 
  (H : L1 ~ L2) : sum_of_squares L1 = sum_of_squares L2 
    := by induction H with
      | nil => rfl
      | cons _ _ Sum12 => simp [sum_of_squares, Sum12]
      | swap x y _ => simp [sum_of_squares, ← add_assoc, ← add_assoc, add_comm (y  ^ 2) (x ^ 2)]
      | trans _ _ Sum1 Sum2 => rw [Sum1, Sum2]
  
@[simp]
theorem sum_of_squares_erase_golfed {R : Type} [Semiring R] [DecidableEq R] (L : List R) (a : R) (h : a ∈ L) : 
  sum_of_squares L = a ^ 2 + sum_of_squares (List.erase L a) 
    := by rw [sum_of_squares_permut_golfed (List.perm_cons_erase h), sum_of_squares]

@[simp]
theorem sum_of_squares_of_list_mul_golfed {R : Type} [CommSemiring R] 
  (L : List R) (c : R) : sum_of_squares (L.map (c * .)) = c ^ 2 * sum_of_squares L
    := by induction L with
      | nil => simp [sum_of_squares]
      | cons a _ ih => simp [sum_of_squares, ih, mul_add, mul_pow c a 2]

@[simp]
theorem sum_of_squares_of_list_div_golfed {F : Type} [Semifield F] 
  (L : List F) (c : F) : sum_of_squares (L.map (. / c)) = (1 / c ^ 2) * sum_of_squares L 
    := by simp [div_eq_mul_inv, mul_comm _ c⁻¹]
