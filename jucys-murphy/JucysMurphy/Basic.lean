import Mathlib



open Equiv


abbrev S (n : ℕ) := Perm (Fin n)
abbrev A (n : ℕ) := MonoidAlgebra ℂ (S n)


noncomputable def jmElem (k n : ℕ) [NeZero n] : A n :=
  ∑ i : Fin n with ↑i ∈ Finset.range (k - 1), MonoidAlgebra.of ℂ (S n) (swap i (k - 1))


lemma σ_eq_comm {n : ℕ} [NeZero n] (σ : S n) (i : Fin n) (hσ : σ (n - 1) = n - 1) :
    σ * (swap i (n-1)) = (swap (σ i) (n-1)) * σ := by
  nth_rw 2 [hσ.symm]

  rw [Perm.mul_def, Perm.mul_def]

  rw [(Equiv.symm_trans_swap_trans i (n-1) σ).symm] -- Päälemma
  rw [Equiv.trans_assoc, (Equiv.trans_assoc σ σ.symm (Equiv.trans (swap i (n-1)) σ)).symm] -- cancellaa sigmat
  simp


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


theorem jmElem_succ_comm_S_n' (n : ℕ) [NeZero n] (σ : S n) (hσ : σ (n - 1) = n - 1) :
    Commute (jmElem n n) (MonoidAlgebra.of ℂ (S n) σ) := by
  rw [jmElem, commute_iff_eq]

  -- Distributivity
  rw [Finset.mul_sum]

  -- Coercion to MonoidAlgebra multiplicative
  -- En tiiä miten rw summan sisällä mutta tää ainaki toimii
  conv =>
    enter [2, 2, i]
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

def lift_perm {n : ℕ} : S n →* S (n + 1) := Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb)

def lift_monAlg {n : ℕ} : A n →ₐ[ℂ] A (n + 1) := MonoidAlgebra.mapDomainAlgHom ℂ ℂ lift_perm

-- Tarvitaanko näitä kahta? -Into
-- Ehkä joo jos halutaan siirtää permutaatioita S (n + 1) → S n.
lemma lift_perm_inj {n : ℕ} : Function.Injective ↑(@lift_perm n) :=
  Equiv.Perm.viaEmbeddingHom_injective (Fin.castSuccEmb)

lemma lift_monAlg_inj {n : ℕ} : Function.Injective ↑(@lift_monAlg n) :=
  Finsupp.mapDomain_injective (@lift_perm_inj n)


-- En iha oo varma onko tää järkevin tapa
def kth_lift_perm {n k : ℕ} : S n →* S (n + k) :=
  match k with
  | 0 => MonoidHom.id (S n)
  | 1 => lift_perm
  | k + 1 => lift_perm ∘ kth_lift_perm

def kth_lift_monAlg {n k : ℕ} [NeZero k]: A n →ₐ[ℂ] A (n + k) :=
  match k with
  | 0 => AlgHom.id ℂ (A n)
  | 1 => lift_monAlg
  | k + 1 => lift_monAlg ∘ kth_lift_monAlg



-- TÄÄ MYÖS UTILS
@[simp]
lemma lift_monAlg_of_eq_of_lift_perm {n : ℕ} (σ : S n) :
    lift_monAlg (MonoidAlgebra.of ℂ (S n) σ) = MonoidAlgebra.of ℂ (S (n + 1)) (lift_perm σ) := by
  unfold lift_monAlg
  simp


theorem jmElem_succ_comm_S_n (n : ℕ) [NeZero n] (σ : S n) :
    Commute (jmElem (n + 1) (n + 1)) (lift_monAlg (MonoidAlgebra.of ℂ (S n) σ)) := by

  have h_range : (-1 : Fin (n + 1)) ∉ Set.range Fin.castSuccEmb := by
    rw [Fin.coe_castSuccEmb, Fin.range_castSucc]
    simp

  have h_lift_σ : lift_perm σ (↑(n + 1) - 1) = (↑(n + 1) - 1) := by
    unfold lift_perm
    simp
    rw [Perm.viaEmbeddingHom_apply]
    exact Perm.viaEmbedding_apply_of_not_mem σ Fin.castSuccEmb (-1) h_range

  rw [lift_monAlg_of_eq_of_lift_perm]
  exact jmElem_succ_comm_S_n' (n + 1) (lift_perm σ) h_lift_σ


theorem jmElem_succ_comm_A_n (n : ℕ) [NeZero n] (a : A n) :
    Commute (jmElem (n + 1) (n + 1)) (lift_monAlg a) := by
  -- Decompose into sum of singles
  rw [← a.sum_single]

  unfold Finsupp.sum

  -- Move lift_monAlg inside sum
  rw [map_sum lift_monAlg]

  -- Move a x out of lift_monAlg
  conv in fun x ↦ _ =>
    intro x
    rw [← mul_one (a x)]
    rw [← MonoidAlgebra.smul_single' (a x) x 1]
    rw [map_smul]

  rw [commute_iff_eq]

  -- Move multiplication by jmElem inside the sums
  rw [Finset.mul_sum, Finset.sum_mul]

  conv in fun i ↦ _ =>
    intro i
    rw [mul_smul_comm]
    tactic => have comm_perm := jmElem_succ_comm_S_n n i
    tactic => simp at comm_perm
    rw [comm_perm]
    rw [← smul_mul_assoc]


theorem jmElem_comm (n k l : ℕ) [NeZero n] :
    Commute (jmElem k n) (jmElem l n) := by
  by_cases h_eq : k = l
  · rw [h_eq]

  suffices h : (x y : ℕ) → x < y → Commute (jmElem x n) (jmElem y n) by
    by_cases h_lt : k < l
    · exact h k l h_lt
    · simp at h_lt
      have h_lt : l < k := lt_of_le_of_ne' h_lt h_eq
      apply Commute.symm
      exact h l k h_lt

  intro k l h_lt



  -- BRUH
  -- About X_nsucc_comm_with_C_S_n input jmElem' m k




-- All Jucys-Murphy elements belonging to ℂ[Sₙ]
def jmElem_set (n : ℕ) : Set (A n) := {↑(jmElem m) | (m : ℕ) ∈ Set.Icc 2 n}

-- In Lean, the structure generated by some set is called the `adjoin`
def jmElem_subAlg (n : ℕ) : Subalgebra ℂ (A n) := Algebra.adjoin ℂ (jmElem_set n)

#check CommRing

-- There is no instance for a commutative algebra, but algebras are implemented
-- as `Semiring`s with some properties so `CommSemiRing` instance suffices.
instance jmeElem_adjoin_comm (n : ℕ) : CommRing (jmElem_subAlg n) := by
  ...
