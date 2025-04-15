import Mathlib

open Equiv

abbrev S (n : ℕ) := Perm (Fin (n+1))

variable (n : ℕ)

example : (Group (S n)) := by exact Perm.permGroup

example (σ : S n) : σ⁻¹ * σ = 1 := by
  group

example (a b : Fin (n+1)) : swap a b = swap b a := by
  have := swap_comm a b
  exact this

#check MonoidAlgebra ℂ (S n)

def jmElem : Fin n → MonoidAlgebra ℂ (S n) := by sorry --fun k ↦ ∑ i ∈ Fin k, swap i (k - 1)

theorem X_n_commutes_with_C_S_n_1 (X_n : jmElem n) (s : MonoidAlgebra ℂ (S n-1)) :
    X_n * s = s * X_n := by
  sorry
