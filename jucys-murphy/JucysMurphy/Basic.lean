import Mathlib



open Equiv


abbrev S (n : ℕ) := Perm (Fin n)
abbrev A (n : ℕ) := MonoidAlgebra ℂ (S n)

--variable (n : ℕ)[n_ne_zero : NeZero n]

example : (Group (S n)) := by exact Perm.permGroup
noncomputable example : Algebra ℂ (MonoidAlgebra ℂ (S (n-1))) := by exact MonoidAlgebra.algebra


example (σ : S n) : σ⁻¹ * σ = 1 := by
  group

example (a b : Fin n) : swap a b = swap b a := by
  exact swap_comm a b

#check MonoidAlgebra ℂ (S n)

noncomputable def jmElem (n : ℕ) [NeZero n]: MonoidAlgebra ℂ (S n) := ∑ i : Fin n with ↑i ∈ Finset.range (n-1), MonoidAlgebra.of ℂ (S n) (swap i (n-1))

noncomputable def jmElem' (k n : ℕ) [NeZero n] : A n := ∑ i ∈ Finset.Ico 0 (n - 1), MonoidAlgebra.of ℂ (S n) (swap i (k-1))
-- Tarvitaa viel k restricted 2,3,...,n


lemma σ_eq_comm {n : ℕ} [NeZero n] : ∀ σ : (S n), ∀ i : Fin n, (σ (n-1) = (n-1)) → σ * (swap i (n-1)) = (swap (σ i) (n-1)) * σ := by
  intro σ i hσ
  nth_rw 2 [hσ.symm]

  rw [Perm.mul_def, Perm.mul_def]

  rw [(Equiv.symm_trans_swap_trans i (n-1) σ).symm] -- Päälemma
  rw [Equiv.trans_assoc, (Equiv.trans_assoc σ σ.symm (Equiv.trans (swap i (n-1)) σ)).symm] -- cancellaa sigmat
  simp

#check Finset.sum_congr
#check Finset.sum_equiv
#check Fintype.sum_equiv


-- TODO: Ei toimi nyt uudella S n määritelmällä: korjaa sitten ku kaikki määritelmät selvinny
lemma σ_sum_perm_eq {n : ℕ} [NeZero n] : ∀ σ : (S n), (σ (n-1) = (n-1)) →
    ∑ i : Fin n with ↑i ∈ Finset.range (n-1), MonoidAlgebra.of ℂ (S n) (swap (σ i) (n-1))
      = ∑ i : Fin n with ↑i ∈ Finset.range (n-1), MonoidAlgebra.of ℂ (S n) (swap i (n-1)) := by

  intro σ hσ

  -- We want to use Finset.sum_equiv σ with the following f, g and of course σ.
  let f : Fin (n+1) → MonoidAlgebra ℂ (S n) := fun k ↦ MonoidAlgebra.of ℂ (S n) (swap (σ k) n)
  let g : Fin (n+1) → MonoidAlgebra ℂ (S n) := fun k ↦ MonoidAlgebra.of ℂ (S n) (swap k n)

  have h_lt_iff : ∀ i : Fin n, i ∈ {i | ↑i ∈ Finset.range (n-1)} ↔ σ i ∈ {i : Fin n | ↑i ∈ Finset.range (n-1)} := by
    intro i
    constructor
    · intro h
      simp at h ⊢
      apply @Fin.val_lt_last (n-1) (σ i)

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
  have h_sum_eq : ∑ i ∈ {i : Fin n | ↑i ∈ Finset.range (n-1)}, (f i) = ∑ i ∈ {i : Fin n | ↑i ∈ Finset.range (n-1)}, (g i) := Finset.sum_equiv σ h_lt_iff h_comp_eq

  unfold f g at h_sum_eq
  exact h_sum_eq





-- Jooh jmElem ei halua toimia idk miks, joten auki kirjotettu
theorem jmElem_succ_comm_S_n' (n : ℕ) [NeZero n] (σ : S n) : (σ (n-1) = (n-1)) → jmElem n * (MonoidAlgebra.of ℂ (S n) σ) =
      (MonoidAlgebra.of ℂ (S n) σ) * jmElem n := by

  unfold jmElem
  intro hσ
  -- Distributivity
  rw [Finset.mul_sum]

  -- Coercion to MonoidAlgebra multiplicative
  -- En tiiä miten rw summan sisällä mutta tää ainaki toimii
  conv =>
    rhs
    rhs
    intro i
    rw [(MonoidHom.map_mul (MonoidAlgebra.of ℂ (S n)) σ (swap i (↑n - 1))).symm]
    rw [σ_eq_comm σ i hσ]
    rw [MonoidHom.map_mul (MonoidAlgebra.of ℂ (S n)) (swap (σ i) (↑n - 1)) σ]

  conv =>
    rhs
    rw [←Finset.sum_mul]

  -- Use the reordering lemma
  rw [σ_sum_perm_eq]
  exact hσ



















-- Before `Utils` compiles:

noncomputable section

def lift_sym {n : ℕ} : S n →* S (n + 1) := Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb)

def lift_mon {n : ℕ} : A n →ₐ[ℂ] A (n + 1) := MonoidAlgebra.mapDomainAlgHom ℂ ℂ lift_sym


lemma lift_sym_inj {n : ℕ} : Function.Injective ↑(@lift_sym n) :=
  Equiv.Perm.viaEmbeddingHom_injective (Fin.castAddEmb 1)

lemma lift_mon_inj {n : ℕ} : Function.Injective ↑(@lift_mon n) :=
  Finsupp.mapDomain_injective (@lift_sym_inj n)



-- TÄÄ MYÖS UTILS
@[simp]
lemma lift_mon_lift_sym_comm_MonAlg_of {n : ℕ} (σ : S n) : lift_mon (MonoidAlgebra.of ℂ (S n) σ) = MonoidAlgebra.of ℂ (S (n + 1)) (lift_sym σ) := by
  unfold lift_mon
  simp




#check Set.range Fin.castSuccEmb

theorem jmElem_succ_comm_S_n (n : ℕ) [NeZero n] (σ : S n) :
    Commute (jmElem (n + 1)) (lift_mon (MonoidAlgebra.of ℂ (S n) σ)) := by

  have h_range : (-1 : Fin (n + 1)) ∉ Set.range Fin.castSuccEmb := by
    rw [Fin.coe_castSuccEmb, Fin.range_castSucc]
    simp

  have h_lift_σ : lift_sym σ (↑(n + 1) - 1) = (↑(n + 1) - 1) := by
    unfold lift_sym
    simp
    rw [Perm.viaEmbeddingHom_apply]
    exact Perm.viaEmbedding_apply_of_not_mem σ Fin.castSuccEmb (-1) h_range

  rw [lift_mon_lift_sym_comm_MonAlg_of]
  exact jmElem_succ_comm_S_n' (n + 1) (lift_sym σ) h_lift_σ


theorem jmElem_succ_comm_A_n (n : ℕ) [NeZero n] (a : A n) :
    Commute (jmElem (n + 1)) (lift_mon a) := by
  --apply MonoidAlgebra.of_commute

  sorry

  -- variable (lift_sym σ : Perm (Fin (n + 1))) (Fin.castSuccEmb : Fin (n + 1) ↪ Fin (n + 1))
  -- theorem viaEmbedding_apply_of_not_mem
  --   (Fin.last n : Fin (n + 1)) (hx : Fin.last n ∉ Set.range Fin.castSuccEmb) :
  --     σ.viaEmbedding Fin.castSuccEmb (Fin.last n) = Fin.last n :=
  --   extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx


  -- viaEmbedding_apply
  --  σ.viaEmbedding Fin.castSuccEmb (Fin.castSuccEmb (Fin.last (n - 1))) = Fin.castSuccEmb (σ (Fin.last (n - 1)))

  -- have := X_n_commutes_with_S_n_1' (n + 1) (lift_sym σ)



-- Given proof h that group element a is in center and element of the algebra f, get a proof that ↑a and f commute.
#check MonoidAlgebra.of_commute



theorem X_n_comm_X_m (n m k : ℕ) [NeZero k]:
    (jmElem' n k) * (jmElem' m k) = (jmElem' m k) * (jmElem' n k) := by
    by_cases h_leq : n ≤ m
    · by_cases h_eq : n = m
      · rw [h_eq]
      · have h_le : n < m := lt_of_le_of_ne h_leq h_eq


    -- BRUH
    -- About X_nsucc_comm_with_C_S_n input jmElem' m k
