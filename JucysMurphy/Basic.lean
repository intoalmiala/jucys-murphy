import Mathlib
import JucysMurphy.Utils

open Equiv

noncomputable section

def jucysMurphyElem (k n : ℕ) [NeZero n] : A n :=
  ∑ i : Fin n with ↑i ∈ Finset.range (k - 1), A_of (swap i ↑(k - 1))

abbrev X := jucysMurphyElem

theorem X_def {k n : ℕ} [NeZero n] : X k n = ∑ i :
    Fin n with ↑i ∈ Finset.range (k - 1), A_of (swap i ↑(k - 1)) := rfl

-- Needed for rewriting jucsyMurphyElem
lemma sum_fin_eq_sum_range {M : Type} [AddCommMonoid M] {n m : ℕ} [NeZero n]
    (h_le : m ≤ n) (f : Fin n → M) :
    ∑ i : Fin n with ↑i ∈ Finset.range m, f i = ∑ i ∈ Finset.range m, f (i : Fin n) := by
  simp
  apply Finset.sum_nbij Fin.val
  · simp
  · exact Function.Injective.injOn Fin.val_injective
  · simp  -- Tähä saa varmaa suoremmanki mut tää toimii
    unfold Set.SurjOn
    intro x hx
    simp at hx
    have h_lt := lt_of_lt_of_le hx h_le
    use ⟨x, h_lt⟩
    exact ⟨hx, rfl⟩
  · simp

-- This lemma only sums over the part which σ actually permutes: `σ_sum_perm_eq` takes
-- care of the fixed part
lemma σ_sum_perm_eq_aux {n m k : ℕ} (hn_lt_m : n < m) [NeZero m] (σ : S n) :
    ∑ i : Fin m with ↑i ∈ Finset.range n, A_of (swap (Perm.castLTHom hn_lt_m σ i) k)
      = ∑ i : Fin m with ↑i ∈ Finset.range n, A_of (swap i k) := by
  -- Suffices to show that σ' maps the sets we sum over to each other
  suffices h_lt_iff : ∀ i : Fin m, i ∈ {i | ↑i ∈ Finset.range n} ↔
      Perm.castLTHom hn_lt_m σ i ∈ {i : Fin m | ↑i ∈ Finset.range n}
  · apply Finset.sum_equiv (Perm.castLTHom hn_lt_m σ)
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
    let i_subtype : ↑(Set.range (Fin.castLEEmb $ le_of_lt hn_lt_m)) := ⟨i, by simp; exact h⟩
    let i_fin_n : Fin n := (Fin.castLEEmb $ le_of_lt hn_lt_m).invOfMemRange i_subtype
    have hi_eq_lift_i_fin_n : (Fin.castLEEmb $ le_of_lt hn_lt_m) i_fin_n = i := by
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
    have hi_not_in_range : i ∉ Set.range ↑(Fin.castLEEmb $ le_of_lt hn_lt_m) := by
      simp
      exact Nat.le_of_not_lt h_ge
    rw [σ.viaEmbedding_apply_of_not_mem (Fin.castLEEmb $ le_of_lt hn_lt_m) i hi_not_in_range] at h
    exact h_ge h

-- This also could be generalized to sum up to any `l` with `n ≤ l < m`
-- but there is really no need
lemma σ_sum_perm_eq {n m k : ℕ} (h_lt : n < m) [NeZero m] (σ : S n) :
    ∑ i : Fin m with ↑i ∈ Finset.range (m - 1), A_of (swap (Perm.castLTHom h_lt σ i) k)
      = ∑ i : Fin m with ↑i ∈ Finset.range (m - 1), A_of (swap i k) := by
  -- To use the main lemma, we need to write these in another form
  rw [sum_fin_eq_sum_range (by simp)]
  rw [sum_fin_eq_sum_range (by simp)]
  rw [Finset.range_eq_Ico] -- Change to use intervals instead
  -- We need 0 ≤ n, n ≤ m - 1 to split the sum at n
  have h_zero_le_n : 0 ≤ n := by exact Nat.zero_le n
  have h_n_le_mpred : n ≤ m - 1 := by exact Nat.le_sub_one_of_lt h_lt
  -- MAIN LEMMA
  rw [←Finset.sum_Ico_consecutive _ h_zero_le_n h_n_le_mpred]
  rw [←Finset.sum_Ico_consecutive _ h_zero_le_n h_n_le_mpred]
  -- Rewrite the first parts back: these equal by auxiliary lemma
  rw [←Finset.range_eq_Ico] -- Change back to use ranges
  rw [←(sum_fin_eq_sum_range (le_of_lt h_lt) (fun x => A_of (swap (((Perm.castLTHom h_lt) σ) ↑x) ↑k)))]
  rw [←(sum_fin_eq_sum_range (le_of_lt h_lt) (fun x => A_of (swap ↑x ↑k)))]
  rw [σ_sum_perm_eq_aux] -- Use the auxiliary lemma
  rw [add_right_inj] -- Cancel
  -- Now using the fact that the lifted permutation fixes everything not in range, we are done
  unfold Perm.castLTHom Perm.castLEHom
  rw [σ.viaEmbeddingHom_apply]
  have hi_not_in_range : ∀ i ∈ Finset.Ico n (m - 1), ↑i ∉ Set.range ↑(Fin.castLEEmb $ le_of_lt h_lt) := by
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

theorem jucysMurphyElem_comm_lt_perm {n m : ℕ} [NeZero n] [NeZero m] (σ : S n) (h_lt : n < m) :
    Commute (X m m) (MonoidAlgebra.castLTHom h_lt (A_of σ)) := by
  rw [X_def, commute_iff_eq]
  -- Distributivity
  rw [Finset.mul_sum]
  conv =>
    enter [2, 2, i]
    rw [MonoidAlgebra.castLTHom_apply]
    rw [←MonoidHom.map_mul A_of (Perm.castLTHom h_lt σ) (swap i ↑(m - 1))]
    rw [Perm.castLTHom_swap_eq_swap_castLTHom]
    rw [MonoidHom.map_mul A_of (swap (Perm.castLTHom h_lt σ i) ↑(m - 1))]
  conv =>
    rhs
    rw [←Finset.sum_mul]
  -- Use the reordering lemma
  rw [σ_sum_perm_eq]
  -- lift_perm same as lift_monAlg
  rw [MonoidAlgebra.castLTHom_apply]

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

lemma MonoidAlgebra.castLEHom_eq {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (n_le_m : n ≤ m) (k_le_n : k ≤ n) : MonoidAlgebra.castLEHom n_le_m (X k n) = X k m := by
  unfold X jucysMurphyElem
  rw [map_sum] -- Linearity
  rw [sum_fin_eq_sum_range (Nat.le_trans (Nat.le_trans (by simp) k_le_n) n_le_m)] -- This is again needed since we want to sum over a Fintype very often
  rw [sum_fin_eq_sum_range (Nat.le_trans (by simp) k_le_n)]
  apply Finset.sum_congr
  · rfl
  · intro i hi
    rw [MonoidAlgebra.castLEHom_apply]
    congr
    simp at hi
    apply Perm.castLEHom_swap_eq
    · -- Can't get linarith to do this nicely so a bit verbose
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_pred hi) k_le_n
    · refine lt_of_lt_of_le ?_ k_le_n
      simp
      exact Nat.pos_of_neZero k

lemma MonoidAlgebra.castLTHom_eq {n m k : ℕ} [NeZero n] [NeZero m] [NeZero k]
    (n_lt_m : n < m) (k_le_n : k ≤ n) : MonoidAlgebra.castLTHom n_lt_m (X k n) = X k m :=
  MonoidAlgebra.castLEHom_eq (le_of_lt n_lt_m) k_le_n

-- This is one of the two main results
theorem jucysMurphyElem_comm_lt_monoidAlgebra {n m : ℕ} [NeZero m] [NeZero n]
    (a : A n) (h_lt : n < m) : Commute (X m m) (MonoidAlgebra.castLTHom h_lt a) := by
  -- Decompose into sum of singles
  rw [← a.sum_single]
  unfold Finsupp.sum
  -- Move lift_monAlg inside sum
  rw [map_sum $ MonoidAlgebra.castLTHom h_lt]
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
    tactic => have comm_perm := jucysMurphyElem_comm_lt_perm i h_lt
    tactic => simp at comm_perm
    rw [comm_perm]
    rw [← smul_mul_assoc]

lemma jucysMurphyElem_comm_of_le_comm {n m k l : ℕ} [NeZero n] [NeZero m] [NeZero k] [NeZero l]
    (n_le_m : n ≤ m) (k_le_n : k ≤ n) (l_le_n : l ≤ n)  (h_comm : Commute (X k n) (X l n)) :
    Commute (X k m) (X l m) := by
  repeat rw [← MonoidAlgebra.castLEHom_eq n_le_m]
  rw [commute_iff_eq] at *
  repeat rw [← map_mul $ MonoidAlgebra.castLEHom n_le_m]
  rw [h_comm]
  all_goals assumption

lemma jucysMurphyElem_comm' {n k l : ℕ} [NeZero n] [NeZero k] [NeZero l]
    (hl_le_n : l ≤ n) (hk_lt_l : k < l) : Commute (X k n) (X l n) := by
  have l_pred_le_n : l - 1 ≤ n := le_trans (by simp) hl_le_n
  have l_pred_nz : NeZero (l - 1) := by
    apply NeZero.of_pos
    simp
    have k_nz : k > 0 := Nat.pos_of_neZero k
    exact Nat.lt_of_le_of_lt k_nz hk_lt_l
  have h_lt : l - 1 < l := Nat.sub_one_lt_of_lt hk_lt_l
  suffices h : Commute (MonoidAlgebra.castLTHom h_lt $ X k (l - 1)) (X l l) by
    rw [MonoidAlgebra.castLTHom_eq h_lt] at h
    · exact jucysMurphyElem_comm_of_le_comm hl_le_n (by linarith) (by linarith) h
    · exact Nat.le_pred_of_lt hk_lt_l
  exact (jucysMurphyElem_comm_lt_monoidAlgebra (X k (l - 1)) h_lt).symm

theorem jucysMurphyElem_comm {n k l : ℕ} [NeZero n] [NeZero k] [NeZero l]
    (h_le : l ≤ n ∧ k ≤ n) : Commute (X k n) (X l n) := by
  by_cases h_eq : k = l
  · rw [h_eq]
  suffices h : k < l → Commute (X k n) (X l n) by
    by_cases h_lt : k < l
    · exact h h_lt
    · simp at h_lt
      have h_lt : l < k := lt_of_le_of_ne' h_lt h_eq
      exact (jucysMurphyElem_comm' h_le.right h_lt).symm
  intro h_lt
  exact jucysMurphyElem_comm' h_le.left h_lt

-- All Jucys-Murphy elements belonging to ℂ[Sₙ]
def jucysMurphyElem_set (n : ℕ) [NeZero n] : Set (A n) :=
  {x | ∃ (m : ℕ), m ∈ Set.Icc 1 n ∧ x = X m n}

-- In Lean, the structure generated by some set is called the `adjoin`
def jucysMurphyElem_subalgebra (n : ℕ) [NeZero n] : Subalgebra ℂ (A n) :=
  Algebra.adjoin ℂ (jucysMurphyElem_set n)


-- To be precise, we call an algebra commutative if the underlying semiring of this
-- (the structure we get when forgetting scalar multiplication) is commutative
instance jucysMurphyElem_adjoin_comm (n : ℕ) [NeZero n] :
    CommSemiring (jucysMurphyElem_subalgebra n) := by
  -- MAIN LEMMA: Underlying semiring of a subalgebra commutative if generators commute
  apply Algebra.adjoinCommSemiringOfComm
  intro a ha b hb
  unfold jucysMurphyElem_set at ha hb
  simp at ha hb
  obtain ⟨k, hk_ge_and_le, ha_eq⟩ := ha
  obtain ⟨hk_ge, hk_le⟩ := hk_ge_and_le
  obtain ⟨l, hl_ge_and_le, hb_eq⟩ := hb
  obtain ⟨hl_ge, hl_le⟩ := hl_ge_and_le
  rw [ha_eq, hb_eq]
  have : NeZero k := ⟨by linarith⟩
  have : NeZero l := ⟨by linarith⟩
  exact jucysMurphyElem_comm (by constructor; exact hl_le; exact hk_le)
