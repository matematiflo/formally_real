/- # Formally real semirings -/

 import Mathlib.NumberTheory.Cyclotomic.Basic
 -- import Mathlib.Tactic

 open BigOperators

/- ## Sums of squares

To define formally real semirings, we first define what it means to be a sum of squares in a semiring. -/

 def sum_of_squares {A : Type _} [Semiring A] {n : ℕ} : (Fin n → A) → A :=
   fun f => ∑ i , (f i) ^ 2

 @[mk_iff]
 class IsFormallyReal (A : Type _) [Semiring A] : Prop where
  is_formally_real : ∀ (n : ℕ), ∀ (f : Fin n → A), (sum_of_squares f = 0) → (∀ i, f i = 0)

def is_sum_of_squares {α : Type _} [Semiring α] (S : α) : Prop := ∃ n : ℕ, ∃ f : Fin n → α, sum_of_squares f = S

-- def sum_sq_add_sum_sq_is_sum_sq [Semiring A] (S1 S2 : A) (h1 : is_sum_of_squares S1) (h2 : is_sum_of_squares S2) : is_sum_of_squares (S1 + S2) := by sorry

 -- **TASK 0:** Prove the above result.

/- ## Properties of formally real semirings 

We first want to show that, if `A` is a *non-trivial* formally real ring, then -1 is not a sum of squares in `A`. 

We deduce it from the more general fact that, if `A` is a formally real nontrivial *semiring*, then there does *not* exist a sum of squares `S` in `A` such that `S + 1 = 0`.-/

def sum_sq_neq_minus_one {A : Type _} [Semiring A] [ntA : Nontrivial A] : IsFormallyReal A → (∀ n : ℕ, ∀ f : Fin n → A, (sum_of_squares f) + 1 ≠ 0) := by
  intro hA n f
  by_contra hf
  let S := sum_of_squares f + 1
  have hS1 : S = sum_of_squares f + 1 := by rfl
  have g : Fin (n + 1) → A := Fin.snoc f 1
  have hS2 : sum_of_squares g = S := by
    simp [sum_of_squares]
    sorry
  have hS3 : S = 0 := by rw [← hf]
  sorry

/- As an example, we show that ordered semirings are formally real. -/

 -- **TASK 1:** Prove the above claim.

 /- Next, we show that a non-trivial formally real semiring is of characteristic 0. -/

 -- **TASK 2:** Prove the above claim.

 /- ## Formally real semifields 
 
 We prove that, in a semifield, the converse to `sum_sq_neq_minus_one` holds, namely: if there is no sum of squares `S` such that `1 + S = 0`, then the semifield is formally real. -/

 section Formally_real_semifields

 def sum_of_sq_eq_zero_iff_all_zero {F : Type _} [Semifield F] [BEq F] : (∀ n : ℕ, ∀ f : Fin n → F, (sum_of_squares f) + 1 ≠ 0) → IsFormallyReal F := sorry

 -- **TASK 3:** Prove the above claim.

 /- In particular, **a field `F` is formally real if and only if `-1` is not a sum of squares in `F`**. -/

 def formally_real_semifield_equiv {F : Type _} [Semifield F] [BEq F] : (IsFormallyReal F) ↔ (∀ n : ℕ, ∀ f : Fin n → F, (sum_of_squares f) + 1 ≠ 0) := by
   constructor
   · exact sum_sq_neq_minus_one
   · exact sum_of_sq_eq_zero_iff_all_zero
   done 

 /- ## Positive cones -/

 section Positive_cones

 -- We define positive cones and show how maximal positive cones induce orderings.


 /- ## Artin-Schreier theory -/

 /- We show that formally real fields admit an ordering, not unique in general.
 In particular, **a field `F` is formally real if and only if it admits an ordering.** -/

