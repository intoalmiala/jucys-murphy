import Mathlib

open Equiv

noncomputable section

abbrev S (n : ℕ) := Perm (Fin n)
abbrev A (n : ℕ) := MonoidAlgebra ℂ (S n)
abbrev A_of {n : ℕ} := MonoidAlgebra.of ℂ (S n)

def lift_perm {k n : ℕ} (h_le : k ≤ n) : S k →* S n :=
  Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h_le)

def lift_MonoidAlgebra {k n : ℕ} (h_le : k ≤ n) : A k →ₐ[ℂ] A n :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (lift_perm h_le)

lemma le_lift_monAlg_perm_eq_le_lift_perm {n m : ℕ} {h_le : n ≤ m} {σ : S n} :
    lift_MonoidAlgebra h_le (A_of σ) = A_of (lift_perm h_le σ) := by
  unfold lift_MonoidAlgebra
  simp


def lift_perm' {k n : ℕ} (h_lt : k < n) : S k →* S n :=
  lift_perm (le_of_lt h_lt)

def lift_MonoidAlgebra' {k n : ℕ} (h_lt : k < n) : A k →ₐ[ℂ] A n :=
  lift_MonoidAlgebra (le_of_lt h_lt)

-- Tarviiko näitä? Jos käyttäis vaa `unfold lt_lift_perm le_lift_perm`?
theorem lt_lift_perm_def {k n : ℕ} (h_lt : k < n) :
    lift_perm' h_lt = Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb $ le_of_lt h_lt) :=
  rfl

theorem lt_lift_monAlg_def {k n : ℕ} (h_lt : k < n) : lift_MonoidAlgebra' h_lt =
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ (Perm.viaEmbeddingHom (Fin.castLEEmb $ le_of_lt h_lt)) :=
  rfl


lemma lt_lift_monAlg_perm_eq_lt_lift_perm {n m : ℕ} {h_lt : n < m} {σ : S n} :
    lift_MonoidAlgebra' h_lt (A_of σ) = A_of (lift_perm' h_lt σ) := by
  rw [lt_lift_monAlg_def, lt_lift_perm_def]
  simp


lemma le_lift_perm_inj {n k : ℕ} (h_le : k ≤ n) : Function.Injective ↑(lift_perm h_le) :=
  Perm.viaEmbeddingHom_injective (Fin.castLEEmb h_le)

lemma le_lift_monAlg_inj {n k : ℕ} (h_le : k ≤ n) : Function.Injective ↑(lift_MonoidAlgebra h_le) :=
  MonoidAlgebra.mapDomain_injective (le_lift_perm_inj h_le)
