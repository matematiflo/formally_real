import Mathlib.Data.Matrix.Basic

#check Nat

def L1 : List ℕ := [1,2,3]
def L2 : List ℤ := [-1,-2,-2]

#eval L2[1]

def A : List (List ℤ) := [[1,2],[-2,3]]

#eval A
#eval A[1]
#eval A[1][0]

def B : List (List ℤ) := [[1,2],[-2,3]]

#eval L1.length
#eval A.length
#eval A[1].length

#eval L2 = L1
#eval L2 = L2
-- #eval L1 = L2 -- type mismatch

#eval A = B

example : A = B := rfl

#eval A + B


