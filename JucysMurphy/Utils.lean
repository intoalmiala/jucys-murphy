
import Mathlib

open Equiv

noncomputable section

abbrev S (n : ℕ) := Perm (Fin n)
abbrev A (n : ℕ) := MonoidAlgebra ℂ (S n)
abbrev A_of {n : ℕ} := MonoidAlgebra.of ℂ (S n)

#check Perm.viaEmbedding_apply

def Perm.castLEHom {k n : ℕ} (h_le : k ≤ n) : S k →* S n :=
  Perm.viaEmbeddingHom (Fin.castLEEmb h_le)

def MonoidAlgebra.castLEHom {k n : ℕ} (h_le : k ≤ n) : A k →ₐ[ℂ] A n :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (Perm.castLEHom h_le)

theorem MonoidAlgebra.castLEHom_apply {n m : ℕ} {h_le : n ≤ m} {σ : S n} :
    MonoidAlgebra.castLEHom h_le (A_of σ) = A_of (Perm.castLEHom h_le σ) := by
  unfold MonoidAlgebra.castLEHom
  simp

def Perm.castLTHom {k n : ℕ} (h_lt : k < n) : S k →* S n :=
  Perm.castLEHom (le_of_lt h_lt)

def MonoidAlgebra.castLTHom {k n : ℕ} (h_lt : k < n) : A k →ₐ[ℂ] A n :=
  MonoidAlgebra.castLEHom (le_of_lt h_lt)

theorem MonoidAlgebra.castLTHom_apply {n m : ℕ} {h_lt : n < m} {σ : S n} :
    MonoidAlgebra.castLTHom h_lt (A_of σ) = A_of (Perm.castLTHom h_lt σ) := by
  unfold Perm.castLTHom MonoidAlgebra.castLTHom
  exact MonoidAlgebra.castLEHom_apply

open scoped Perm in
lemma castLTHom_swap_eq_swap_castLTHom {n m : ℕ} [NeZero n] [NeZero m]
    (h_lt : n < m) (σ : S n) (i : Fin m) : (Perm.castLTHom h_lt) σ * swap i ↑(m - 1) =
      (swap (Perm.castLTHom h_lt σ i) ↑(m - 1)) * (Perm.castLTHom h_lt) σ := by
  -- Really long way of saying that `σ` fixes `m - 1`
  nth_rw 2 [←σ.viaEmbedding_apply_of_not_mem
    (Fin.castLEEmb $ le_of_lt h_lt)
    ↑(m - 1)
    (by simp; exact Nat.le_sub_one_of_lt h_lt)]
  -- Change the unfolded definitions back
  change (Perm.castLTHom h_lt) σ * swap i ↑(m - 1) =
    swap (Perm.castLTHom h_lt σ i) ((Perm.castLTHom h_lt σ) ↑(m - 1)) * (Perm.castLTHom h_lt) σ

  rw [Equiv.mul_swap_eq_swap_mul] -- Main lemma
