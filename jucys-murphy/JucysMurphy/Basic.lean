import Mathlib



open Equiv

abbrev S (n : ℕ) := Perm (Fin (n+1))
abbrev A (n : ℕ) := MonoidAlgebra ℂ (S n)

variable (n : ℕ)

example : (Group (S n)) := by exact Perm.permGroup

example (σ : S n) : σ⁻¹ * σ = 1 := by
  group

example (a b : Fin (n+1)) : swap a b = swap b a := by
  exact swap_comm a b

#check MonoidAlgebra ℂ (S n)

noncomputable def jmElem : MonoidAlgebra ℂ (S n) := ∑ i : Fin (n+1) with ↑i ∈ Finset.range n, MonoidAlgebra.of ℂ (S n) (swap i n)

--def to_elem_of_bigger {G : Type} [Group G] {H : Subgroup G} : (MonoidAlgebra H) → MonoidAlgebra G


-- Tarvitaan että ℂ[H] subalgebra ℂ[G] ja sitten tää voidaan kirjottaa
--lemma h_comm_of_comm {G : Type} [Group G] (H : Subgroup G) :

lemma σ_eq_comm : ∀ σ : (S n), ∀ i : Fin (n+1), (σ n = n) → σ * (swap i n) = (swap (σ i) n) * σ := by
  intro σ i hσ
  nth_rw 2 [hσ.symm]

  rw [Perm.mul_def, Perm.mul_def]

  rw [(Equiv.symm_trans_swap_trans i n σ).symm] -- Päälemma
  rw [Equiv.trans_assoc, (Equiv.trans_assoc σ σ.symm (Equiv.trans (swap i ↑n) σ)).symm] -- cancellaa sigmat
  simp

#check Finset.sum_congr
#check Finset.sum_equiv
#check Fintype.sum_equiv


lemma σ_sum_perm_eq : ∀ σ : (S n), (σ n = n) → ∑ i : Fin (n+1) with ↑i ∈ Finset.range n, MonoidAlgebra.of ℂ (S n) (swap (σ i) n) = ∑ i : Fin (n+1) with ↑i ∈ Finset.range n, MonoidAlgebra.of ℂ (S n) (swap i n) := by
  intro σ hσ

  -- We want to use Finset.sum_equiv σ with the following f, g and of course σ.
  let f : Fin (n+1) → MonoidAlgebra ℂ (S n) := fun k ↦ MonoidAlgebra.of ℂ (S n) (swap (σ k) n)
  let g : Fin (n+1) → MonoidAlgebra ℂ (S n) := fun k ↦ MonoidAlgebra.of ℂ (S n) (swap k n)

  have h_lt_iff : ∀ i : Fin (n+1), i ∈ {i : Fin (n+1) | ↑i ∈ Finset.range n} ↔ σ i ∈ {i : Fin (n+1) | ↑i ∈ Finset.range n} := by
    intro i
    constructor
    · intro h
      simp_all
      apply Fin.val_lt_last
      by_contra h_eq
      rw [hσ.symm] at h_eq
      apply σ.injective at h_eq
      rw [h_eq] at h
      exact (lt_self_iff_false ↑(Fin.last n)).mp h
    · intro h
      simp_all
      apply Fin.val_lt_last
      by_contra h_eq
      rw [h_eq] at h
      rw [hσ] at h
      exact (lt_self_iff_false ↑(Fin.last n)).mp h

  have h_comp_eq : ∀ i ∈ {i : Fin (n+1) | ↑i ∈ Finset.range n}, f i = g (σ i) := by
    unfold f g
    intro i hi
    rfl

  -- Ei välttis tarvii mut sitä varten jos Lean ei tunnista f ja g implisiittisesti
  -- En ymmärrä miks Finset.sum_equiv ei toimi?
  have h_sum_eq : ∑ i ∈ {i : Fin (n+1) | ↑i ∈ Finset.range n}, (f i) = ∑ i ∈ {i : Fin (n+1) | ↑i ∈ Finset.range n}, (g i) := Finset.sum_equiv σ h_lt_iff h_comp_eq

  unfold f g at h_sum_eq
  exact h_sum_eq







/-
  Tavat jotenka formalisoida ℂ [S (n-1)]:
    - Tämä on alimoduuli jolla on algebran rakenne
    - Tämä on alialgebra

  Halutaan:
    - Tämä on
-/

-- Jooh jmElem ei halua toimia idk miks, joten auki kirjotettu
theorem X_n_commutes_with_S_n_1 (σ : S n) : (σ n = n) → (∑ i : Fin (n+1) with ↑i ∈ Finset.range n, MonoidAlgebra.of ℂ (S n) (swap i n)) * (MonoidAlgebra.of ℂ (S n) σ) = (MonoidAlgebra.of ℂ (S n) σ) * (∑ i : Fin (n+1) with ↑i ∈ Finset.range n, MonoidAlgebra.of ℂ (S n) (swap i n)) := by
  intro hσ
  -- Distributivity
  rw [Finset.mul_sum]

  -- Coercion to MonoidAlgebra multiplicative
  -- En tiiä miten rw summan sisällä mutta tää ainaki toimii
  conv =>
    rhs
    rhs
    intro i
    rw [(MonoidHom.map_mul (MonoidAlgebra.of ℂ (S n)) σ (swap i ↑n)).symm]
    rw [σ_eq_comm n σ i hσ]

  -- Convert back and factor σ
  conv =>
    rhs
    rhs
    intro i
    rw [MonoidHom.map_mul (MonoidAlgebra.of ℂ (S n)) (swap (σ i) ↑n) σ]

  conv =>
    rhs
    rw [←Finset.sum_mul]

  -- Use the reordering lemma
  rw [σ_sum_perm_eq]
  exact hσ









-- Given proof h that group element a is in center and element of the algebra f, get a proof that ↑a and f commute.
#check MonoidAlgebra.of_commute

theorem X_n_commutes_with_C_S_n_1 (s : MonoidAlgebra ℂ (S (n-1))) :
    jmElem * s = s * jmElem := by
  sorry
  -- Riittää jos s ∈ S n-1: MonoidAlgebra.of_commute tai kirjota ite
