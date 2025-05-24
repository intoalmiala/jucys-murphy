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

def lt_lift_perm {k n : ℕ} (h_lt : k < n) : S k →* S n :=
  le_lift_perm (le_of_lt h_lt)

def lt_lift_monAlg {k n : ℕ} (h_lt : k < n) : A k →ₐ[ℂ] A n :=
  le_lift_monAlg (le_of_lt h_lt)


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
  ∑ i : Fin n with ↑i ∈ Finset.range (k - 1), A_of n (swap i (k - 1))


lemma σ_swap_eq_swap_σ {n : ℕ} [NeZero n] (σ : S n) (i : Fin n) (hσ : σ (n - 1) = n - 1) :
    σ * (swap i (n-1)) = (swap (σ i) (n-1)) * σ := by
  nth_rw 2 [hσ.symm]

  rw [Perm.mul_def, Perm.mul_def]

  rw [(Equiv.symm_trans_swap_trans i (n-1) σ).symm] -- Päälemma
  rw [Equiv.trans_assoc, (Equiv.trans_assoc σ σ.symm (Equiv.trans (swap i (n-1)) σ)).symm] -- cancellaa sigmat
  simp



lemma σ_sum_perm_eq {n : ℕ} [NeZero n] : ∀ σ : (S (n + 1)), (σ n = n) →
    ∑ i : Fin (n + 1) with ↑i ∈ Finset.range n, A_of (n + 1) (swap (σ i) n)
      = ∑ i : Fin (n + 1) with ↑i ∈ Finset.range n, A_of (n + 1) (swap i n) := by

  intro σ hσ

  -- We want to use Finset.sum_equiv σ with the following f, g and of course σ.
  let f : Fin (n + 1) → MonoidAlgebra ℂ (S (n + 1)) := fun k ↦ A_of (n + 1) (swap (σ k) n)
  let g : Fin (n + 1) → MonoidAlgebra ℂ (S (n + 1)) := fun k ↦ A_of (n + 1) (swap k n)

  have h_lt_iff : ∀ i : Fin (n + 1), i ∈ {i | ↑i ∈ Finset.range n} ↔
      σ i ∈ {i : Fin (n + 1) | ↑i ∈ Finset.range n} := by
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


-- TODO: joko todista tää tai korjaa vanha versio
lemma σ_sum_perm_eq' {n : ℕ} [NeZero n] (σ : S n) :
    ∑ i : Fin (n + 1) with ↑i ∈ Finset.range n, A_of (n + 1) (swap (lift_perm σ i) n)
      = ∑ i : Fin (n + 1) with ↑i ∈ Finset.range n, A_of (n + 1) (swap i n) := by

  have h_lt_iff : ∀ i : Fin (n + 1), i ∈ {i | ↑i ∈ Finset.range n} ↔
      lift_perm σ i ∈ {i : Fin (n + 1) | ↑i ∈ Finset.range n} := by
    intro i
    unfold lift_perm
    simp
    rw [Perm.viaEmbeddingHom_apply]
    constructor
    · intro h_le
      sorry
    · by_contra h_eq
      simp at h_eq
      obtain ⟨h_leq, h_nleq⟩ := h_eq
      have h_eq : n = ↑i := (Nat.eq_of_le_of_lt_succ h_nleq i.isLt).symm

      rw [←h_eq] at h_leq


      #check Perm.viaEmbedding_apply_of_not_mem σ Fin.castSuccEmb
      sorry

    --rw [Perm.viaEmbedding_apply_of_not_mem σ Fin.castSuccEmb i (by simp)]
    --constructor
    --· intro h_le


  sorry




theorem jmElem_succ_comm_perm' (n m : ℕ) (h_lt : n < m) [NeZero m] (σ : S m) (hσ : ∀ k > n, σ k = k) :
    Commute (jmElem m m) (A_of m σ) := by
  rw [jmElem, commute_iff_eq]

  -- Distributivity
  rw [Finset.mul_sum]

  have hσ' : σ (↑m - 1) = ↑m - 1 := by sorry

  -- Coercion to MonoidAlgebra multiplicative
  -- En tiiä miten rw summan sisällä mutta tää ainaki toimii
  conv =>
    enter [2, 2, i]
    rw [(MonoidHom.map_mul (A_of m) σ (swap i (↑m - 1))).symm]
    rw [σ_swap_eq_swap_σ σ i hσ']
    rw [MonoidHom.map_mul (A_of n) (swap (σ i) (↑n - 1)) σ]

  conv =>
    rhs
    rw [←Finset.sum_mul]

  -- Use the reordering lemma
  rw [σ_sum_perm_eq]
  exact hσ


-- TÄÄ MYÖS UTILS
@[simp]
lemma lift_monAlg_of_eq_of_lift_perm {n m : ℕ} (h_lt : n < m) (σ : S n) :
    lt_lift_monAlg h_lt (A_of n σ) = A_of m (lt_lift_perm h_lt σ) := by
  unfold lt_lift_monAlg le_lift_monAlg
  simp
  sorry


theorem jmElem_succ_comm_perm (n m : ℕ) [NeZero n] [NeZero m] (σ : S n) (h_lt : n < m) :
    Commute (jmElem m m) (lt_lift_monAlg h_lt (A_of n σ)) := by

  have h_range : ∀ k > n, (↑k : Fin m) ∉ Set.range (Fin.castLEEmb (le_of_lt h_lt)) := by
    rw [Fin.coe_castLEEmb (le_of_lt h_lt), Fin.range_castLE]
    simp
    sorry

  have h_lift_σ : ∀ k > n, lt_lift_perm h_lt σ ↑k = ↑k := by
    unfold lt_lift_perm le_lift_perm
    rw [Perm.viaEmbeddingHom_apply]
    intro k hk
    exact Perm.viaEmbedding_apply_of_not_mem σ (Fin.castLEEmb $ le_of_lt h_lt) ↑k (h_range k hk)

  rw [lift_monAlg_of_eq_of_lift_perm]
  exact jmElem_succ_comm_perm' n m h_lt (lt_lift_perm h_lt σ) h_lift_σ



-- theorem jmElem_succ_comm_monAlg (n : ℕ) [NeZero n] (a : A n) :
--    Commute (jmElem (n + 1) (n + 1)) (lift_monAlg a) := by
theorem jmElem_succ_comm_monAlg (n m : ℕ) [NeZero m] [NeZero n] (a : A n) (h_lt : n < m) :
    Commute (jmElem m m) (le_lift_monAlg (le_of_lt h_lt) a) := by
  -- Decompose into sum of singles
  rw [← a.sum_single]

  unfold Finsupp.sum

  -- Move lift_monAlg inside sum
  rw [map_sum $ le_lift_monAlg (le_of_lt h_lt)]

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
    tactic => have comm_perm := jmElem_succ_comm_perm n m i h_lt
    tactic => simp at comm_perm
    rw [comm_perm]
    rw [← smul_mul_assoc]


#check Function.Injective.invOfMemRange

--set_option diagnostics true

theorem jmElem_comm (n k l : ℕ) [NeZero n] :
    Commute (jmElem k n) (jmElem l n) := by
  by_cases h_eq : k = l
  · rw [h_eq]

  suffices h : (x y : ℕ) → x < y → Commute (jmElem x n) (jmElem y n) by
    by_cases h_lt : k < l
    · exact h k l h_lt
    · simp at h_lt
      have h_lt : l < k := lt_of_le_of_ne' h_lt h_eq
      exact (h l k h_lt).symm

  intro k l h_lt

  have h_k_le_n : l - 1 ≤ n := sorry
  have h_nz : NeZero (l - 1) := sorry
  have h_l_nz : NeZero l := sorry

  have : jmElem k n ∈ Set.range (le_lift_monAlg h_k_le_n) := by
    simp
    use jmElem k (l - 1)
    sorry

  suffices h : Commute (le_lift_monAlg (by simp) $ jmElem k (l - 1)) (jmElem l l) by sorry

  have h_l : l - 1 + 1 = l := by sorry
  have := jmElem_succ_comm_monAlg (l - 1) l (jmElem k (l - 1))
  simp at this
  rw [h_l] at this

  exact Commute.symm (jmElem_succ_comm_monAlg (l - 1) (jmElem k (l - 1)))

  -- jmElem k n ∈ ℂ[S (l - 1)]
  -- jmElem_succ_comm_A_n ==> tulos

  sorry

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
