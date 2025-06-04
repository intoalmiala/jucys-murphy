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

-- Needed for rewriting jucsyMurphyElem
lemma sum_fin_eq_sum_nat {M : Type} [AddCommMonoid M] {n m : ℕ} [NeZero n]
    (h_le : m ≤ n) (f : Fin n → M) :
    ∑ i : Fin n with ↑i ∈ Finset.range m, f i = ∑ i ∈ Finset.range m, f (i : Fin n) := by
  simp
  apply Finset.sum_nbij Fin.val
  · simp
  · exact Function.Injective.injOn Fin.val_injective
  · simp
    unfold Set.SurjOn
    intro x hx
    simp at hx
    have h_lt := lt_of_lt_of_le hx h_le
    use ⟨x, h_lt⟩
    exact ⟨hx, rfl⟩
  · simp

-- This lemma only sums over the part which σ actually permutes: `σ_sum_perm_eq` takes
-- care of the fixed part
lemma Perm.lt_sum_swap_castLTHom_eq_sum_swap {n m k : ℕ} (n_lt_m : n < m) [NeZero m] (σ : S n) :
    ∑ i : Fin m with ↑i ∈ Finset.range n, A_of (swap (Perm.castLTHom n_lt_m σ i) k)
      = ∑ i : Fin m with ↑i ∈ Finset.range n, A_of (swap i k) := by
  -- Suffices to show that σ' maps the sets we sum over to each other
  suffices h_lt_iff : ∀ i : Fin m, i ∈ {i | ↑i ∈ Finset.range n} ↔
      Perm.castLTHom n_lt_m σ i ∈ {i : Fin m | ↑i ∈ Finset.range n}
  · apply Finset.sum_equiv (Perm.castLTHom n_lt_m σ)
    · simp at h_lt_iff ⊢ -- Basically holds by definition
      exact h_lt_iff
    · intro i hi -- Also basically by definition
      rfl
  simp
  -- This should be obvious by definition of lifting permutations.
  -- However, this is made difficult since there does not exist a general
  -- `Fin.castPred` for arbitrary descents like there is for arbitrary lifts: `Fin.castLEEmb`
  intro i
  constructor <;> intro h
  · unfold Perm.castLTHom Perm.castLEHom
    rw [Perm.viaEmbeddingHom_apply]
    -- To use `Perm.viaEmbedding_apply`, we need to take the pre-image of i under Fin.castLEEmb.
    -- This is quite annoying to do. Is there a better way?
    let i_subtype : ↑(Set.range (Fin.castLEEmb $ le_of_lt n_lt_m)) := ⟨i, by simp; exact h⟩
    let i_fin_n : Fin n := (Fin.castLEEmb $ le_of_lt n_lt_m).invOfMemRange i_subtype
    have hi_eq_lift_i_fin_n : (Fin.castLEEmb $ le_of_lt n_lt_m) i_fin_n = i := by
      unfold i_fin_n
      simp
      rfl
    rw [←hi_eq_lift_i_fin_n]
    rw [σ.viaEmbedding_apply]
    simp
  · unfold Perm.castLTHom Perm.castLEHom at h
    rw [Perm.viaEmbeddingHom_apply] at h
    -- This direction is a bit easier since lifted permutations fix elements not
    -- in range of the embedding
    by_contra h_ge
    have hi_not_in_range : i ∉ Set.range ↑(Fin.castLEEmb $ le_of_lt n_lt_m) := by
      simp
      exact Nat.le_of_not_lt h_ge
    rw [σ.viaEmbedding_apply_of_not_mem (Fin.castLEEmb $ le_of_lt n_lt_m) i hi_not_in_range] at h
    exact h_ge h

-- This also could be generalized to sum up to any `l` with `n ≤ l < m`
-- but there is really no need
lemma Perm.sum_swap_castLTHom_eq_sum_swap {n m k : ℕ} (h_lt : n < m) [NeZero m] (σ : S n) :
    ∑ i : Fin m with ↑i ∈ Finset.range (m - 1), A_of (swap (Perm.castLTHom h_lt σ i) k)
      = ∑ i : Fin m with ↑i ∈ Finset.range (m - 1), A_of (swap i k) := by
  -- To use the main lemma, we need to write these in another form
  rw [sum_fin_eq_sum_nat (by simp)]
  rw [sum_fin_eq_sum_nat (by simp)]
  rw [Finset.range_eq_Ico] -- Change to use intervals instead
  -- We need 0 ≤ n, n ≤ m - 1 to split the sum at n
  have h_zero_le_n : 0 ≤ n := by exact Nat.zero_le n
  have h_n_le_mpred : n ≤ m - 1 := by exact Nat.le_sub_one_of_lt h_lt
  -- MAIN LEMMA
  rw [← Finset.sum_Ico_consecutive _ h_zero_le_n h_n_le_mpred]
  rw [← Finset.sum_Ico_consecutive _ h_zero_le_n h_n_le_mpred]
  -- Rewrite the first parts back: these equal by auxiliary lemma
  rw [← Finset.range_eq_Ico] -- Change back to use ranges
  rw [← sum_fin_eq_sum_nat
          (le_of_lt h_lt)
          (fun x => A_of (swap (((Perm.castLTHom h_lt) σ) ↑x) ↑k))]
  rw [← sum_fin_eq_sum_nat (le_of_lt h_lt) (fun x => A_of (swap ↑x ↑k))]
  rw [Perm.lt_sum_swap_castLTHom_eq_sum_swap] -- Use the auxiliary lemma
  rw [add_right_inj] -- Cancel
  -- Now using the fact that the lifted permutation fixes everything not in range, we are done
  unfold Perm.castLTHom Perm.castLEHom
  rw [σ.viaEmbeddingHom_apply]
  have hi_not_in_range :
      ∀ i ∈ Finset.Ico n (m - 1), ↑i ∉ Set.range ↑(Fin.castLEEmb $ le_of_lt h_lt) := by
    simp
    intro i h_ge h_lt
    rw [Nat.mod_eq_of_lt]
    exact h_ge
    exact Nat.lt_of_lt_pred h_lt
  -- Sums equal since sets and elements equal
  apply Finset.sum_congr
  · rfl
  · intro i hi
    rw [σ.viaEmbedding_apply_of_not_mem]
    exact hi_not_in_range i hi

lemma castLEEmb_eq {n m k : ℕ} [NeZero n] [NeZero m] (n_le_m : n ≤ m) (k_lt_n : k < n) :
    Fin.castLEEmb n_le_m ↑k = ↑k := by
  simp
  apply Fin.eq_of_val_eq
  rw [Fin.coe_castLE n_le_m ↑k]
  simp
  rw [Nat.mod_eq_of_lt k_lt_n]
  rw [Nat.mod_eq_of_lt (by linarith)]

lemma Perm.castLEHom_swap_eq {n m i j : ℕ} [NeZero n] [NeZero m]
    (n_le_m : n ≤ m) (i_lt_n : i < n) (j_lt_n : j < n) :
    (Perm.castLEHom n_le_m) (swap ↑i ↑j) = swap ↑i ↑j := by
  unfold Perm.castLEHom
  rw [Perm.viaEmbeddingHom_apply]
  ext x
  by_cases h : ↑x < n
  · let x_subtype : ↑(Set.range (Fin.castLEEmb n_le_m)) := ⟨x, by simp; exact h⟩
    let x_fin_n : Fin n := (Fin.castLEEmb n_le_m).invOfMemRange x_subtype
    have x_eq_lift_i_fin_n : (Fin.castLEEmb n_le_m) x_fin_n = x := by
      unfold x_fin_n
      simp
      rfl
    rw [← x_eq_lift_i_fin_n]
    rw [Perm.viaEmbedding_apply]
    rw [← castLEEmb_eq n_le_m i_lt_n]
    rw [← castLEEmb_eq n_le_m j_lt_n]
    let f := Fin.castLEEmb n_le_m
    rw [← @Function.comp_apply _ _ _ f (swap ↑i ↑j)]
    rw [← @Function.comp_apply _ _ _ (swap (f ↑i) (f ↑j)) f]
    rw [Function.Embedding.swap_comp]
  · have x_not_in_range : x ∉ Set.range ↑(Fin.castLEEmb n_le_m) := by
      simp
      exact Nat.le_of_not_lt h
    simp at h
    rw [(swap ↑i ↑j).viaEmbedding_apply_of_not_mem (Fin.castLEEmb n_le_m) x x_not_in_range]
    rw [swap_apply_of_ne_of_ne]
    · rw [← Fin.val_ne_iff]
      simp
      rw [Nat.mod_eq_of_lt (by linarith)]
      have i_lt_x : i < x := Nat.lt_of_lt_of_le i_lt_n h
      exact Nat.ne_of_lt' i_lt_x
    · rw [← Fin.val_ne_iff]
      simp
      rw [Nat.mod_eq_of_lt (by linarith)]
      have j_lt_x : j < x := Nat.lt_of_lt_of_le j_lt_n h
      exact Nat.ne_of_lt' j_lt_x
