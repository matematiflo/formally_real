/- # Formally real semirings -/

import Mathlib.NumberTheory.Cyclotomic.Basic
-- import Mathlib.Tactic

open BigOperators

/- ## Sums of squares

To define formally real semirings, we first define what it means to be a sum of squares in a semiring. -/

section sums_of_squares

def sum_of_squares {α : Type _} [Semiring α] {n : ℕ} (f : Fin n → α) : α :=
  ∑ i, (f i)^2

-- def sum_of_squares_2 [Semiring α] : List α → α
--   | [] => 0
--   | (a :: l) => (a * a) + (sum_of_squares_2 l)

-- def is_sum_of_squares [Semiring α] (S : α) : Prop := ∃ n : ℕ, ∃ f : Fin n → α, sum_of_squares f = S

-- def is_sum_of_squares_2 [Semiring α] (S : α) : Prop := ∃ L : List α, sum_of_squares_2 L = S

-- inductive is_sum_of_squares_cons [Semiring α] : α → Prop where
--   | zero : is_sum_of_squares_cons (0 : α)
--   | of_add (S a : α) (hS : is_sum_of_squares_cons S) : is_sum_of_squares_cons (S + a^2)

-- def is_sum_of_squares_iff_is_sum_of_squares_cons [Semiring α] (S : α) : is_sum_of_squares S ↔ is_sum_of_squares_2 S := by
--   constructor
--   · intro h
--     simp [is_sum_of_squares] at h
--     rcases h with ⟨n, f, hf⟩
--     simp [is_sum_of_squares_2]
--     have Lf : List α := sorry
--     sorry
--   · sorry    
--   done

@[mk_iff]
class IsFormallyReal {α : Type _} [Semiring α] : Prop where
  is_formally_real : ∀ (n : ℕ), ∀ (f : Fin n → α), (sum_of_squares f = 0) → (∀ i, f i = 0)

def is_sum_of_squares {α : Type _} [Semiring α] (S : α) : Prop := ∃ n : ℕ, ∃ f : Fin n → α, sum_of_squares f = S

-- def sum_sq_neq_minus_one {A : Type _} [Semiring A] [ntA : Nontrivial A] : IsFormallyReal A → (∀ n : ℕ, ∀ f : Fin n → A, 1 + sum_of_squares f ≠ 0) := by 

/- ## Properties of formally real semirings

Next, we give basic properties of sums of squares in semirings. -/

section properties_of_formally_real_semirings

/- We first show that if a *non-trivial* ring A is formally real, then -1 is not a sum of squares. 

More generally, if `A` is a formally real nontrivial *semiring* (so `-1` does not make sense in `A`), then we prove that there does *not* exist a sum of squares `S` in `A` such that `1 + S = 0`. -/

def sum_sq_neq_minus_one {α : Type _} [Semiring α] [nt : Nontrivial α] : IsFormallyReal α → (∀ n : ℕ, ∀ f : Fin n → A, 1 + sum_of_squares f ≠ 0) := by
  sorry



    




/- As an example, we show that ordered semirings are formally real. -/

-- **TASK 1:** Prove the above claim.

/- Next, we show that a non-trivial formally real semiring is of characteristic 0. -/

-- **TASK 2:** Prove the above claim.

/- ## Formally real semifields -/

section Formally_real_semifields

/- We prove that, in a semifield, the converse to `sum_sq_neq_minus_one` holds, namely: if there is no sum of squares `S` such that `1 + S = 0`, then the semifield is formally real. -/

def sum_of_sq_eq_zero_iff_all_zero {F : Type _} [Semifield F] [BEq F] : (∀ n : ℕ, ∀ f : Fin n → F, 1 + sum_sq f ≠ 0) → IsFormallyReal F := sorry

/- In particular, **a field `F` is formally real if and only if `-1` is not a sum of squares in `F`**. -/

def formally_real_semifield_equiv {F : Type _} [Semifield F] [BEq F] : IsFormallyReal F ↔ ∀ n : ℕ, ∀ f : Fin n → F, 1 + sum_sq f ≠ 0 := by
  constructor
  · exact sum_sq_neq_minus_one
  · exact sum_of_sq_eq_zero_iff_all_zero
  done 

def formally_real_field_equiv {F : Type _} [Field F] [BEq F] : IsFormallyReal F ↔ ¬ (∃ n : ℕ, ∃ f : Fin n → F, sum_sq f = -1) := sorry

-- **TASK 3:** Prove the above claim.

/- ## Positive cones -/

section Positive_cones

-- We define positive cones and show how maximal positive cones induce orderings.


/- ## Artin-Schreier theory -/

/- We show that formally real fields admit an ordering, not unique in general.

In particular, **a field `F` is formally real if and only if it admits an ordering.** -/