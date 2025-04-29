import Mathlib

open Equiv

-- abbrev AtMost (n : ℕ) := Fin (n + 1)

abbrev S (n : ℕ) := Perm (Fin n)

variable (n : ℕ) [n_ne_zero : NeZero n]

example : (Group (S n)) := by exact Perm.permGroup

example (σ : S n) : σ⁻¹ * σ = 1 := by
  group

example (a b : Fin (n+1)) : swap a b = swap b a := by
  exact swap_comm a b

noncomputable def jmElem (k : Fin n) := ∑ i < k, MonoidAlgebra.of ℂ (S n) (swap i k)

#check Perm.subtypeCongr
#check {x : Fin (n + 1) // x ≠ n}
#check Fin n
#check Fin.last
#check Fin.ofNat'
#check Fin.coe_neg_one

example : { x : Fin n // ↑x = n - 1 } ⊕ { x : Fin n // ↑x ≠ n - 1 } ≃ Fin n := by
  let p : Fin n → Prop := fun x ↦ ↑x = n - 1
  exact sumCompl p

#check Subtype

example : { x : Fin n // ↑x = n - 1 } ≃ Unit where
  toFun := fun _ ↦ ()
  invFun a := ⟨n - 1, by
    simp
    sorry
  ⟩
  left_inv := by
    unfold Function.LeftInverse
    simp
    intro a ha
    sorry
  right_inv a := by rfl

#check Fin.lt_iff_val_lt_val
#check ∀ a : Fin n, a.val = a.castSucc.val
#check Fin.coe_castSucc
#check Fin.coeSucc_eq_succ
#check Fin.eq_mk_iff_val_eq
#check Fin.mk_eq_mk

example : ↑((n : Fin (n + 1)) + 1) = n + 1 := by
  -- rw [← Fin.eq_mk_iff_val_eq]
  let a : Fin (n + 1) := ↑n
  have h_lt : ↑a <
  have : a = ⟨n + 1, ()⟩ := by sorry
  apply (@Fin.eq_mk_iff_val_eq (n + 2) a (n + 1) (by simp)).mp
  refine ⟨n + 1, ?_⟩
  sorry

#check (n : Fin $ n + 1) + 1
#check Fin.lt_add_one_iff
#check Fin.equivSubtype
#check Equiv.subtypeEquivProp
#check Equiv.trans

theorem fin_n_equiv_subtype : Fin n ≃ { x : Fin (n + 1) // x ≠ Fin.last n } := by
  trans { x : Fin (n + 1) // x < n }
  · exact Fin.equivSubtype
  · sorry

example : Fin n ≃ { x : Fin (n + 1) // x ≠ Fin.last n } where
  toFun a := by
    let a': Fin (n + 1) := a.castSucc
    refine ⟨a', ?_⟩
    rw [Fin.ne_iff_vne]

    by_contra h_eq_succ'
    have h_lt_nat := a.isLt
    have h_nat_eq : (a : ℕ) = ↑a' := Fin.coe_castSucc a
    have h_lt_nat' : ↑a' < n := by
      rw [← h_nat_eq]
      exact h_lt_nat
    rw [h_eq_succ'] at h_lt_nat'
    simp at h_lt_nat'
  invFun := fun a ↦ (a : Fin $ n + 1).castPred a.prop
  left_inv a := by simp
  right_inv := by
    unfold Function.RightInverse Function.LeftInverse
    simp
    intro a ha
    push_neg at ha
    rw [Fin.ne_iff_vne a (Fin.last n)] at ha
    simp at ha
    have := a.isLt
    change ↑a < n.succ at this
    rw [Nat.lt_succ] at this
    have := lt_of_le_of_ne this ha

    have h_n_1_pos : n + 1 ≠ 0 := sorry
    have := (Nat.mod_eq_iff_lt h_n_1_pos).mpr
    sorry

#check Fin.ne_iff_vne
#check Fin.succ
#check Nat.mod_eq_iff_lt
#check Nat.lt_succ
#check subtypeEquivProp
#check permCongr

def lift_to_subtype (σ : Perm (Fin n)) :
    Perm {x : Fin (n + 1) // x ≠ Fin.last n} := by
  have h_equiv : Perm (Fin n) ≃ Perm {x : Fin (n + 1) // x ≠ Fin.last n} := by
    apply permCongr

    sorry
  exact h_equiv.toFun σ


def lift (σ : S n) : S (n + 1) := by
  -- We divide the type AtMost (n + 1) into subtypes,
  -- one corresponding to x ≤ n and one to x = n + 1.
  let p : Fin (n + 1) → Prop := fun x ↦ x = n
  refine @Perm.subtypeCongr (Fin (n + 1)) p _ ?_ ?_ <;> simp [p]
  · -- Case x = n + 1. The subtype is equivalent to Unit.
    have h_unit := ofUnique Unit { a : Fin (n + 1) // a = Fin.last n }
    have h_perm := permCongr h_unit
    exact h_perm.toFun (Equiv.refl Unit)
  · -- Case x ≤ n.
    exact lift_to_subtype n σ

#check MonoidAlgebra.liftNC

noncomputable def lift_algebra_to_succ (x : MonoidAlgebra ℂ (S n)) :
    MonoidAlgebra ℂ (S (n + 1)) :=
  MonoidAlgebra.mapDomain (lift n) x

theorem jmElem_succ_comm (s : MonoidAlgebra ℂ (S n)) :
    jmElem (n + 1) (n + 1) * lift_algebra_to_succ n s =
      lift_algebra_to_succ n s * jmElem (n + 1) (n + 1) := by
  sorry
