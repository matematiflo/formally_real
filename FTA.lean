import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.AlgebraicCard

import Lean

open Lean Elab Tactic

elab "tada" : tactic => do
  let gs ← getUnsolvedGoals
  if gs.isEmpty then
    logInfo "Goals accomplished 🎉"
  else
    Term.reportUnsolvedGoals gs
    throwAbortTactic

example : 1 + 1 = 2 := by
  trivial
  tada

open Matrix
open Fintype


def IsEigenvector [Fintype In] [Field ℂ] (A : Matrix In In ℂ) (v : In → ℂ) := (v ≠ 0) ∧ (∃ μ : ℂ, (mulVec A v) = μ • v)

theorem exists_eigenvector [Fintype In] [Field ℂ] (A : Matrix In In ℂ) : (card In ≥ 1) → (∃ v : In → ℂ, IsEigenvector A v) := 
by
  sorry

/- k= 0 case of the induction -/

/-
variable {m : ℕ} [Fintype (Fin m)] [Field ℂ]

def IsEigenvector (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) := (v ≠ 0) ∧ (∃ μ : ℂ, (mulVec A v) = μ • v)

theorem exists_eigenvector (A : Matrix (Fin m) (Fin m) ℂ) : (m ≥ 1) → (∃ v : Fin m → ℂ, IsEigenvector A v) := 
by
  sorry

-/

lemma exists_eigenvector_in_odd_dim [Fintype n] [Field ℂ] (A : Matrix n n ℂ) : (Odd (card n)) → (∃ v : n → ℂ, IsEigenvector A v) := 
by
  sorry

/- Formalisation of Lemma 3? -/

lemma lemma3 [Field F] [AddCommMonoid V] [Module F V] : (1>0) := 
by
  exact zero_lt_one
  tada

variable (n : Finset ℕ) (k : ℕ) (m : Fintype (Fin k))

#check Fin 3
#check card (Fin 3)

-- m should be denoted Ik
#check m
#check m.1
#check m.2
#check m.card

#check n.1
#check n.2
#check card n

def L : List ℕ := [1,2,2]

#check L
#check List.length L
#eval List.length L
#check L[1]
#eval L[1]

def M : Multiset ℕ := [1,2,2]

#check M
#check Multiset.card M
#eval Multiset.card M

variable (x : Fintype (Fin 3)) [Fintype j]

-- x should be denoted I3
#check x
#check x.1
#check x.2
#check x.card

#check j
#check @j
#check card j


def L2 : List ℤ := [-1,-2,-2]
def L1 : List ℤ := [1,2,3]

def A : List (List ℤ) := [[1,2],[-2,3]]
def I : List (List ℤ) := [[1,0],[0,1]]

#eval A
#eval A[1]
#eval A[1][0]

