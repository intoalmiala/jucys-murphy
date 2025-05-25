import Mathlib



open Equiv


abbrev S (n : ℕ) := Perm (Fin n)
abbrev A (n : ℕ) := MonoidAlgebra ℂ (S n)
noncomputable abbrev A_of (n : ℕ) := MonoidAlgebra.of ℂ (S n)



-- Before `Utils` compiles:

noncomputable section


def kth_lift_perm (n k : ℕ) : S n →* S (n + k) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castAddEmb k)

def kth_lift_monAlg (n k : ℕ) : A n →ₐ[ℂ] A (n + k) :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (kth_lift_perm n k)


lemma kth_lift_perm_inj (n k : ℕ) : Function.Injective ↑(kth_lift_perm n k) :=
  Perm.viaEmbeddingHom_injective (Fin.castAddEmb k)

lemma kth_lift_monAlg_inj (n k : ℕ) : Function.Injective ↑(kth_lift_monAlg n k) :=
  Finsupp.mapDomain_injective (kth_lift_perm_inj n k)


def le_lift_perm {k n : ℕ} (h_le : k ≤ n) : S k →* S n :=
  Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h_le)

def le_lift_monAlg {k n : ℕ} (h_le : k ≤ n) : A k →ₐ[ℂ] A n :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (le_lift_perm h_le)

theorem le_lift_monAlg_def {k n : ℕ} (h_le : k ≤ n) : le_lift_monAlg h_le =
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ (Perm.viaEmbeddingHom (Fin.castLEEmb h_le)) :=
  rfl


def lt_lift_perm {k n : ℕ} (h_lt : k < n) : S k →* S n :=
  le_lift_perm (le_of_lt h_lt)

def lt_lift_monAlg {k n : ℕ} (h_lt : k < n) : A k →ₐ[ℂ] A n :=
  le_lift_monAlg (le_of_lt h_lt)


theorem lt_lift_perm_def {k n : ℕ} (h_lt : k < n) :
    lt_lift_perm h_lt = Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb $ le_of_lt h_lt) :=
  rfl

theorem lt_lift_monAlg_def {k n : ℕ} (h_lt : k < n) : lt_lift_monAlg h_lt =
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ (Perm.viaEmbeddingHom (Fin.castLEEmb $ le_of_lt h_lt)) :=
  rfl

#check AlgHom.comp_apply
#check MonoidHom.

theorem viaEmbeddingHom_comp {α β γ : Type*} (ι : α ↪ β) (κ : β ↪ γ) :
    (Perm.viaEmbeddingHom κ).comp (Perm.viaEmbeddingHom ι) = Perm.viaEmbeddingHom (ι.trans κ) := by
  sorry

theorem le_lift_monAlg_trans {k l n : ℕ} (hkl : k ≤ l) (hln : l ≤ n) {a : A k} :
    le_lift_monAlg hln (le_lift_monAlg hkl a) = le_lift_monAlg (le_trans hkl hln) a := by
  rw [le_lift_monAlg_def, le_lift_monAlg_def]
  have : (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (Perm.viaEmbeddingHom (Fin.castLEEmb hln)))
      ((MonoidAlgebra.mapDomainAlgHom ℂ ℂ (Perm.viaEmbeddingHom (Fin.castLEEmb hkl))) a) =
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (Perm.viaEmbeddingHom (Fin.castLEEmb $ le_trans hkl hln)) a := by
    rw [← AlgHom.comp_apply]
    rw [← MonoidAlgebra.mapDomainAlgHom_comp ℂ ℂ]
    rw [viaEmbeddingHom_comp (Fin.castLEEmb hkl) (Fin.castLEEmb hln)]
    simp
    sorry
  exact this


lemma le_lift_perm_inj {n k : ℕ} (h_le : k ≤ n) : Function.Injective ↑(le_lift_perm h_le) :=
  Perm.viaEmbeddingHom_injective (Fin.castLEEmb h_le)

lemma le_lift_monAlg_inj {n k : ℕ} (h_le : k ≤ n) : Function.Injective ↑(le_lift_monAlg h_le) :=
  MonoidAlgebra.mapDomain_injective (le_lift_perm_inj h_le)


def lift_perm {n : ℕ} : S n →* S (n + 1) := le_lift_perm (by simp)

def lift_monAlg {n : ℕ} : A n →ₐ[ℂ] A (n + 1) := le_lift_monAlg (by simp)

lemma lift_perm_inj {n : ℕ} : Function.Injective ↑(@lift_perm n) :=
  Perm.viaEmbeddingHom_injective (Fin.castSuccEmb)

lemma lift_monAlg_inj {n : ℕ} : Function.Injective ↑(@lift_monAlg n) :=
  Finsupp.mapDomain_injective (@lift_perm_inj n)


noncomputable def jmElem (k n : ℕ) [NeZero n] : A n :=
  ∑ i : Fin n with ↑i ∈ Finset.range (k - 1), A_of n (swap i ↑(k - 1))


lemma σ_swap_eq_swap_σ {n : ℕ} [NeZero n] (σ : S n) (i : Fin n) (hσ : σ ↑(n - 1) = ↑(n - 1)) :
    σ * (swap i ↑(n - 1)) = (swap (σ i) ↑(n - 1)) * σ := by
  nth_rw 2 [← hσ]

  rw [Perm.mul_def, Perm.mul_def]

  rw [← Equiv.symm_trans_swap_trans i ↑(n - 1) σ] -- Päälemma
  rw [Equiv.trans_assoc, ← Equiv.trans_assoc σ σ.symm (Equiv.trans (swap i ↑(n - 1)) σ)] -- cancellaa sigmat
  simp



lemma σ_sum_perm_eq {n m : ℕ} (h_lt : n < m) [NeZero m] : ∀ σ : (S m), (σ n = n) →
    ∑ i : Fin m with ↑i ∈ Finset.range n, A_of m (swap (σ i) n)
      = ∑ i : Fin m with ↑i ∈ Finset.range n, A_of m (swap i n) := by

  intro σ hσ

  -- We want to use Finset.sum_equiv σ with the following f, g and of course σ.
  let f : Fin m → A m := fun k ↦ A_of m (swap (σ k) n)
  let g : Fin m → A m := fun k ↦ A_of m (swap k n)

  have h_lt_iff : ∀ i : Fin m, i ∈ {i | ↑i ∈ Finset.range n} ↔
      σ i ∈ {i : Fin m | ↑i ∈ Finset.range n} := by
    intro i
    constructor
    · intro h
      simp at h ⊢
      apply @Fin.val_lt_last n (σ i)
      rw [←Fin.natCast_eq_last n]

      by_contra h_eq
      rw [hσ.symm] at h_eq
      apply σ.injective at h_eq
      rw [h_eq] at h
      simp at h
    · intro h
      simp_all
      apply Fin.val_lt_last
      by_contra h_eq
      rw [h_eq] at h
      rw [hσ] at h
      simp at h

  have h_comp_eq : ∀ i ∈ {i : Fin (n + 1) | ↑i ∈ Finset.range n}, f i = g (σ i) := by
    unfold f g
    intro i hi
    rfl

  -- Ei välttis tarvii mut sitä varten jos Lean ei tunnista f ja g implisiittisesti
  -- En ymmärrä miks Finset.sum_equiv ei toimi?
  have h_sum_eq : ∑ i ∈ {i : Fin (n + 1) | ↑i ∈ Finset.range n}, (f i) =
      ∑ i ∈ {i : Fin (n + 1) | ↑i ∈ Finset.range n}, (g i) := by
    refine Finset.sum_equiv σ ?_ ?_
    · simp at h_lt_iff ⊢
      exact h_lt_iff
    · simp at h_comp_eq ⊢
      exact h_comp_eq

  unfold f g at h_sum_eq
  exact h_sum_eq

#check Nat.eq_of_le_of_lt_succ

-- TODO: joko todista tää tai korjaa vanha versio
lemma σ_sum_perm_eq' {n m : ℕ} (h_lt : n < m) [NeZero m] (σ : S n) :
    ∑ i : Fin m with ↑i ∈ Finset.range n, A_of m (swap (lift_perm σ i) n)
      = ∑ i : Fin m with ↑i ∈ Finset.range n, A_of m (swap i n) := by

  have h_lt_iff : ∀ i : Fin m, i ∈ {i | ↑i ∈ Finset.range n} ↔
      lt_lift_perm h_lt σ i ∈ {i : Fin m | ↑i ∈ Finset.range n} := by
    intro i
    rw [lt_lift_perm_def]
    simp
    rw [Perm.viaEmbeddingHom_apply]
    constructor
    · intro h_le
      sorry
    · by_contra h_eq
      simp at h_eq
      obtain ⟨h_leq, h_nleq⟩ := h_eq
      have := i.isLt
      -- have h_eq : n = ↑i := (Nat.eq_of_le_of_lt_succ h_nleq i.isLt).symm
      -- rw [←h_eq] at h_leq


      #check Perm.viaEmbedding_apply_of_not_mem σ Fin.castSuccEmb
      sorry

    --rw [Perm.viaEmbedding_apply_of_not_mem σ Fin.castSuccEmb i (by simp)]
    --constructor
    --· intro h_le


  sorry




theorem jmElem_succ_comm_perm' {n m : ℕ} (h_lt : n < m) [NeZero m] (σ : S m) (hσ : ∀ k ∈ Finset.Ico n m, σ k = k) :
    Commute (jmElem m m) (A_of m σ) := by
  rw [jmElem, commute_iff_eq]

  -- Distributivity
  rw [Finset.mul_sum]

  have h_m_pred_mem : m - 1 ∈ Finset.Ico n m := by
    simp
    constructor
    · exact Nat.le_sub_one_of_lt h_lt
    · exact Nat.pos_of_neZero m

  -- Coercion to MonoidAlgebra multiplicative
  -- En tiiä miten rw summan sisällä mutta tää ainaki toimii
  conv =>
    enter [2, 2, i]
    rw [(MonoidHom.map_mul (A_of m) σ (swap i ↑(m - 1))).symm]
    rw [σ_swap_eq_swap_σ σ i (hσ (m - 1) h_m_pred_mem)]
    rw [MonoidHom.map_mul (A_of m) (swap (σ i) ↑(m - 1)) σ]

  conv =>
    rhs
    rw [←Finset.sum_mul]

  have hm : m - 1 < m := Nat.sub_one_lt_of_lt h_lt

  -- Use the reordering lemma
  rw [σ_sum_perm_eq hm]
  exact hσ (m - 1) h_m_pred_mem


-- TÄÄ MYÖS UTILS
@[simp]
lemma lift_monAlg_of_eq_of_lift_perm {n m : ℕ} (h_lt : n < m) (σ : S n) :
    lt_lift_monAlg h_lt (A_of n σ) = A_of m (lt_lift_perm h_lt σ) := by
  rw [lt_lift_monAlg_def, lt_lift_perm_def]
  simp

#check Finset.range

theorem jmElem_succ_comm_perm {n m : ℕ} [NeZero n] [NeZero m] (σ : S n) (h_lt : n < m) :
    Commute (jmElem m m) (lt_lift_monAlg h_lt (A_of n σ)) := by

  have h_range : ∀ k ∈ Finset.Ico n m, (↑k : Fin m) ∉ Set.range (Fin.castLEEmb (le_of_lt h_lt)) := by
    rw [Fin.coe_castLEEmb (le_of_lt h_lt), Fin.range_castLE]
    intro k hk
    simp at *
    rw [Nat.mod_eq_of_lt hk.right]
    exact hk.left

  have h_lift_σ : ∀ k ∈ Finset.Ico n m, lt_lift_perm h_lt σ ↑k = ↑k := by
    unfold lt_lift_perm le_lift_perm
    rw [Perm.viaEmbeddingHom_apply]
    intro k hk
    exact Perm.viaEmbedding_apply_of_not_mem σ (Fin.castLEEmb $ le_of_lt h_lt) ↑k (h_range k hk)

  rw [lift_monAlg_of_eq_of_lift_perm]
  exact jmElem_succ_comm_perm' h_lt (lt_lift_perm h_lt σ) h_lift_σ



-- theorem jmElem_succ_comm_monAlg (n : ℕ) [NeZero n] (a : A n) :
--    Commute (jmElem (n + 1) (n + 1)) (lift_monAlg a) := by
theorem jmElem_succ_comm_monAlg {n m : ℕ} [NeZero m] [NeZero n] (a : A n) (h_lt : n < m) :
    Commute (jmElem m m) (lt_lift_monAlg h_lt a) := by
  -- Decompose into sum of singles
  rw [← a.sum_single]

  unfold Finsupp.sum

  -- Move lift_monAlg inside sum
  rw [map_sum $ lt_lift_monAlg h_lt]

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
    tactic => have comm_perm := jmElem_succ_comm_perm i h_lt
    tactic => simp at comm_perm
    rw [comm_perm]
    rw [← smul_mul_assoc]


#check Function.Injective.invOfMemRange

--set_option diagnostics true

lemma jmElem_comm' {n k l : ℕ} [NeZero n] [NeZero k] [NeZero l] (h_le : l ≤ n) (h_lt : k < l) :
    Commute (jmElem k n) (jmElem l n) := by

  have l_pred_le_n : l - 1 ≤ n := le_trans (by simp) h_le

  have l_pred_nz : NeZero (l - 1) := by
    apply NeZero.of_pos
    simp
    have k_nz : k > 0 := Nat.pos_of_neZero k
    exact Nat.lt_of_le_of_lt k_nz h_lt

  have h_lt : l - 1 < l := Nat.sub_one_lt_of_lt h_lt

  suffices h : Commute (lt_lift_monAlg h_lt $ jmElem k (l - 1)) (jmElem l l) by

    sorry

  exact (jmElem_succ_comm_monAlg (jmElem k (l - 1)) h_lt).symm


theorem jmElem_comm {n k l : ℕ} [NeZero n] [NeZero k] [NeZero l] (h_le : l ≤ n ∧ k ≤ n):
    Commute (jmElem k n) (jmElem l n) := by
  by_cases h_eq : k = l
  · rw [h_eq]

  suffices h : k < l → Commute (jmElem k n) (jmElem l n) by
    by_cases h_lt : k < l
    · exact h h_lt
    · simp at h_lt
      have h_lt : l < k := lt_of_le_of_ne' h_lt h_eq
      exact (jmElem_comm' h_le.right h_lt).symm

  intro h_lt
  exact jmElem_comm' h_le.left h_lt

  -- BRUH
  -- About X_nsucc_comm_with_C_S_n input jmElem' m k


-- All Jucys-Murphy elements belonging to ℂ[Sₙ]
def jmElem_set (n : ℕ) [NeZero n] : Set (A n) := {x | ∃ (m : ℕ), m ∈ Set.Icc 2 n ∧ x = jmElem m n}

-- In Lean, the structure generated by some set is called the `adjoin`
def jmElem_subAlg (n : ℕ) [NeZero n] : Subalgebra ℂ (A n) := Algebra.adjoin ℂ (jmElem_set n)

#check CommRing

-- There is no instance for a commutative algebra, but algebras are implemented
-- as `Semiring`s with some properties so `CommSemiRing` instance suffices.
instance jmeElem_adjoin_comm (n : ℕ) [NeZero n] : CommRing (jmElem_subAlg n) := by
  sorry
