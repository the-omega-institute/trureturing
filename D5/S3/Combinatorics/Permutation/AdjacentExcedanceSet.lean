/- GID: D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/AdjacentExcedanceSet
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The adjacent excedance and nonexcedance count splits into a swap and two order-preserving deletions. -/

import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet

open Equiv

/-- Every strict excedance position is prescribed by the given set. -/
def HasExactExcedances {n : ℕ} (p : Perm (Fin n)) (S : Set (Fin n)) : Prop :=
  ∀ j, j < p j ↔ j ∈ S

abbrev ExactPermutations {n : ℕ} (S : Set (Fin n)) :=
  {p : Perm (Fin n) // HasExactExcedances p S}

/-- The cardinality of the finite set of actual permutations with the prescribed positions. -/
noncomputable def exactCount {n : ℕ} (S : Set (Fin n)) : ℕ :=
  Nat.card (ExactPermutations S)

def swapPositions {n : ℕ} (a b : Fin n) : Perm (Perm (Fin n)) :=
  (Equiv.swap a b).equivCongr (Equiv.refl (Fin n))

private def extendAt {n : ℕ} (b : Fin (n + 1)) (p : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  p.extendDomain (finSuccAboveEquiv b)

private theorem extendAt_fixed {n : ℕ} (b : Fin (n + 1)) (p : Perm (Fin n)) :
    extendAt b p b = b :=
  Equiv.Perm.extendDomain_apply_not_subtype p (finSuccAboveEquiv b) (by simp)

private theorem extendAt_succAbove {n : ℕ} (b : Fin (n + 1)) (p : Perm (Fin n)) (i : Fin n) :
    extendAt b p (b.succAbove i) = b.succAbove (p i) :=
  Equiv.Perm.extendDomain_apply_image p (finSuccAboveEquiv b) i

private def restrictComplement {n : ℕ} (b : Fin (n + 1))
    (p : {p : Perm (Fin (n + 1)) // p b = b}) :
    Perm {j : Fin (n + 1) // j ≠ b} :=
  p.val.subtypeEquiv fun j => by
    constructor
    · intro hj h
      exact hj (p.val.injective (h.trans p.property.symm))
    · intro hj h
      exact hj ((congrArg p.val h).trans p.property)

private def deleteAt {n : ℕ} (b : Fin (n + 1))
    (p : {p : Perm (Fin (n + 1)) // p b = b}) : Perm (Fin n) :=
  (finSuccAboveEquiv b).symm.permCongr (restrictComplement b p)

private theorem deleteAt_succAbove {n : ℕ} (b : Fin (n + 1))
    (p : {p : Perm (Fin (n + 1)) // p b = b}) (i : Fin n) :
    b.succAbove (deleteAt b p i) = p.val (b.succAbove i) := by
  change ((finSuccAboveEquiv b) ((finSuccAboveEquiv b).symm
    (restrictComplement b p (finSuccAboveEquiv b i)))).val = p.val (b.succAbove i)
  rw [Equiv.apply_symm_apply] <;> rfl

private def fixedAtEquiv {n : ℕ} (b : Fin (n + 1)) :
    {p : Perm (Fin (n + 1)) // p b = b} ≃ Perm (Fin n) where
  toFun := deleteAt b
  invFun p := ⟨extendAt b p, extendAt_fixed b p⟩
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro j
    change extendAt b (deleteAt b p) j = p.val j
    by_cases hj : j = b
    · subst j
      rw [extendAt_fixed, p.property]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [extendAt_succAbove, deleteAt_succAbove]
  right_inv p := by
    apply Equiv.ext
    intro i
    change deleteAt b ⟨extendAt b p, extendAt_fixed b p⟩ i = p i
    apply (Fin.strictMono_succAbove b).injective
    rw [deleteAt_succAbove]
    exact extendAt_succAbove b p i

private theorem exact_delete_iff {n : ℕ} (b : Fin (n + 1)) (S : Set (Fin (n + 1)))
    (hb : b ∉ S) (p : {p : Perm (Fin (n + 1)) // p b = b}) :
    HasExactExcedances p.val S ↔
      HasExactExcedances (fixedAtEquiv b p) (b.succAbove ⁻¹' S) := by
  change HasExactExcedances p.val S ↔ HasExactExcedances (deleteAt b p) (b.succAbove ⁻¹' S)
  constructor
  · intro hp i
    have h := hp (b.succAbove i)
    rw [← deleteAt_succAbove b p i, Fin.succAbove_lt_succAbove_iff] at h
    exact h
  · intro hp j
    by_cases hj : j = b
    · subst j
      simp [p.property, hb]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [← deleteAt_succAbove b p i, Fin.succAbove_lt_succAbove_iff]
      exact hp i

def deleteFixedCase {n : ℕ} (b : Fin (n + 1)) (S : Set (Fin (n + 1)))
    (hb : b ∉ S) :
    {p : ExactPermutations S // p.val b = b} ≃ ExactPermutations (b.succAbove ⁻¹' S) :=
  let reorder :
      {p : ExactPermutations S // p.val b = b} ≃
        {p : {p : Perm (Fin (n + 1)) // p b = b} // HasExactExcedances p.val S} :=
    { toFun := fun p => ⟨⟨p.val.val, p.property⟩, p.val.property⟩
      invFun := fun p => ⟨⟨p.val.val, p.property⟩, p.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  reorder.trans ((fixedAtEquiv b).subtypeEquiv (exact_delete_iff b S hb))

private theorem exact_swap_iff {n : ℕ} (a : Fin (n + 1)) (S : Set (Fin (n + 2)))
    (hl : a.castSucc ∈ S) (hr : a.succ ∉ S) (p : Perm (Fin (n + 2))) :
    (HasExactExcedances p S ∧ p a.castSucc ≠ a.succ ∧ p a.succ ≠ a.succ) ↔
      HasExactExcedances (swapPositions a.castSucc a.succ p)
        ((Equiv.swap a.castSucc a.succ) ⁻¹' S) := by
  constructor
  · rintro ⟨hp, hxne, hyne⟩
    have hx : a.succ < p a.castSucc :=
      lt_of_le_of_ne (Fin.castSucc_lt_iff_succ_le.mp ((hp _).mpr hl)) hxne.symm
    have hynot : ¬ a.succ < p a.succ := fun h => hr ((hp a.succ).mp h)
    have hy : p a.succ ≤ a.castSucc :=
      Fin.le_castSucc_iff.symm.mp (lt_of_le_of_ne (le_of_not_gt hynot) hyne)
    intro j
    change j < p (Equiv.swap a.castSucc a.succ j) ↔ Equiv.swap a.castSucc a.succ j ∈ S
    by_cases hjl : j = a.castSucc
    · subst j
      rw [Equiv.swap_apply_left]
      exact iff_of_false (not_lt_of_ge hy) hr
    · by_cases hjr : j = a.succ
      · subst j
        rw [Equiv.swap_apply_right]
        exact iff_of_true hx hl
      · rw [Equiv.swap_apply_of_ne_of_ne hjl hjr]
        exact hp j
  · intro hp
    have hx := hp a.succ
    change a.succ < p (Equiv.swap a.castSucc a.succ a.succ) ↔
      Equiv.swap a.castSucc a.succ a.succ ∈ S at hx
    rw [Equiv.swap_apply_right] at hx
    have hy := hp a.castSucc
    change a.castSucc < p (Equiv.swap a.castSucc a.succ a.castSucc) ↔
      Equiv.swap a.castSucc a.succ a.castSucc ∈ S at hy
    rw [Equiv.swap_apply_left] at hy
    have hx' : a.succ < p a.castSucc := hx.mpr hl
    have hy' : p a.succ < a.succ := Fin.le_castSucc_iff.symm.mpr (le_of_not_gt (hr ∘ hy.mp))
    refine ⟨?_, ne_of_gt hx', ne_of_lt hy'⟩
    intro j
    by_cases hjl : j = a.castSucc
    · subst j
      exact iff_of_true (a.castSucc_lt_succ.trans hx') hl
    · by_cases hjr : j = a.succ
      · subst j
        exact iff_of_false (not_lt_of_ge hy'.le) hr
      · have h := hp j
        change j < p (Equiv.swap a.castSucc a.succ j) ↔ Equiv.swap a.castSucc a.succ j ∈ S at h
        rwa [Equiv.swap_apply_of_ne_of_ne hjl hjr] at h

private theorem adjacent_left_unique {n : ℕ} (a : Fin (n + 1)) (p : Perm (Fin (n + 2)))
    (hx : p a.castSucc = a.succ) : p a.succ ≠ a.succ :=
  fun hy => a.castSucc_lt_succ.ne (p.injective (hx.trans hy.symm))

theorem exact_swap_fixed_iff {n : ℕ} (a : Fin (n + 1)) (S : Set (Fin (n + 2)))
    (hl : a.castSucc ∈ S) (hr : a.succ ∉ S) (p : Perm (Fin (n + 2))) :
    (HasExactExcedances p S ∧ p a.castSucc = a.succ) ↔
      (HasExactExcedances (swapPositions a.castSucc a.succ p) (S \ {a.castSucc}) ∧
        swapPositions a.castSucc a.succ p a.succ = a.succ) := by
  constructor
  · rintro ⟨hp, hx⟩
    have hyne := adjacent_left_unique a p hx
    have hynot : ¬ a.succ < p a.succ := fun h => hr ((hp a.succ).mp h)
    have hy : p a.succ ≤ a.castSucc :=
      Fin.le_castSucc_iff.symm.mp (lt_of_le_of_ne (le_of_not_gt hynot) hyne)
    constructor
    · intro j
      change j < p (Equiv.swap a.castSucc a.succ j) ↔ j ∈ S \ {a.castSucc}
      by_cases hjl : j = a.castSucc
      · subst j
        rw [Equiv.swap_apply_left]
        exact iff_of_false (not_lt_of_ge hy) (by simp)
      · by_cases hjr : j = a.succ
        · subst j
          rw [Equiv.swap_apply_right, hx]
          exact iff_of_false (lt_irrefl _) (fun h => hr h.1)
        · rw [Equiv.swap_apply_of_ne_of_ne hjl hjr]
          simpa [Set.mem_diff, hjl] using hp j
    · change p (Equiv.swap a.castSucc a.succ a.succ) = a.succ
      rwa [Equiv.swap_apply_right]
  · rintro ⟨hp, hfix⟩
    change p (Equiv.swap a.castSucc a.succ a.succ) = a.succ at hfix
    rw [Equiv.swap_apply_right] at hfix
    have hy := hp a.castSucc
    change a.castSucc < p (Equiv.swap a.castSucc a.succ a.castSucc) ↔
      a.castSucc ∈ S \ {a.castSucc} at hy
    rw [Equiv.swap_apply_left] at hy
    have hy' : p a.succ ≤ a.castSucc := le_of_not_gt fun h => by simpa using hy.mp h
    refine ⟨?_, hfix⟩
    intro j
    by_cases hjl : j = a.castSucc
    · subst j
      rw [hfix]
      exact iff_of_true a.castSucc_lt_succ hl
    · by_cases hjr : j = a.succ
      · subst j
        exact iff_of_false (not_lt_of_ge (hy'.trans a.castSucc_lt_succ.le)) hr
      · have h := hp j
        change j < p (Equiv.swap a.castSucc a.succ j) ↔ j ∈ S \ {a.castSucc} at h
        rw [Equiv.swap_apply_of_ne_of_ne hjl hjr] at h
        simpa [Set.mem_diff, hjl] using h

theorem delete_swap_set {n : ℕ} (a : Fin (n + 1)) (S : Set (Fin (n + 2)))
    (hr : a.succ ∉ S) :
    a.succ.succAbove ⁻¹' (S \ {a.castSucc}) = a.castSucc.succAbove ⁻¹' S := by
  ext i
  change a.succ.succAbove i ∈ S \ {a.castSucc} ↔ a.castSucc.succAbove i ∈ S
  rcases lt_trichotomy i a with h | rfl | h
  · have hne : i.castSucc ≠ a.castSucc := (Fin.castSucc_lt_castSucc_iff.mpr h).ne
    rw [Fin.succAbove_succ_of_le _ _ h.le, Fin.succAbove_castSucc_of_lt _ _ h]
    simp [Set.mem_diff, hne]
  · rw [Fin.succAbove_succ_self, Fin.succAbove_castSucc_self]
    simp [hr]
  · have hne : i.succ ≠ a.castSucc := (Fin.castSucc_lt_succ_iff.mpr h.le).ne.symm
    rw [Fin.succAbove_succ_of_lt _ _ h, Fin.succAbove_castSucc_of_le _ _ h.le]
    simp [Set.mem_diff, hne]

/-- The bracket identity [vbau] = [vabu] + [vbu] + [vau] for actual permutations.
Both smaller sets are pulled back along the order embedding that skips the deleted position. -/
theorem adjacentBA {n : ℕ} (a : Fin (n + 1)) (S : Set (Fin (n + 2)))
    (hl : a.castSucc ∈ S) (hr : a.succ ∉ S) :
    exactCount S =
      exactCount ((Equiv.swap a.castSucc a.succ) ⁻¹' S) +
        exactCount (a.succ.succAbove ⁻¹' S) + exactCount (a.castSucc.succAbove ⁻¹' S) := by
  classical
  let fixesRight (p : ExactPermutations S) : Prop := p.val a.succ = a.succ
  let hitsRightFromLeft (p : {p : ExactPermutations S // ¬fixesRight p}) : Prop :=
    p.val.val a.castSucc = a.succ
  let right := deleteFixedCase a.succ S hr
  let leftCast :
      {p : {p : ExactPermutations S // ¬fixesRight p} // hitsRightFromLeft p} ≃
        {p : Perm (Fin (n + 2)) // HasExactExcedances p S ∧ p a.castSucc = a.succ} :=
    { toFun := fun p => ⟨p.val.val.val, p.val.val.property, p.property⟩
      invFun := fun p => ⟨⟨⟨p.val, p.property.1⟩, adjacent_left_unique a p.val p.property.2⟩,
        p.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let leftFix :
      {p : Perm (Fin (n + 2)) //
        HasExactExcedances p (S \ {a.castSucc}) ∧ p a.succ = a.succ} ≃
        {p : ExactPermutations (S \ {a.castSucc}) // p.val a.succ = a.succ} :=
    { toFun := fun p => ⟨⟨p.val, p.property.1⟩, p.property.2⟩
      invFun := fun p => ⟨p.val.val, p.val.property, p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let left := (leftCast.trans ((swapPositions a.castSucc a.succ).subtypeEquiv
    (exact_swap_fixed_iff a S hl hr))).trans (leftFix.trans
      (deleteFixedCase a.succ (S \ {a.castSucc}) (fun h => hr h.1)))
  let swapCast :
      {p : {p : ExactPermutations S // ¬fixesRight p} // ¬hitsRightFromLeft p} ≃
        {p : Perm (Fin (n + 2)) //
          HasExactExcedances p S ∧ p a.castSucc ≠ a.succ ∧ p a.succ ≠ a.succ} :=
    { toFun := fun p => ⟨p.val.val.val, p.val.val.property, p.property, p.val.property⟩
      invFun := fun p => ⟨⟨⟨p.val, p.property.1⟩, p.property.2.2⟩, p.property.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let swapped := swapCast.trans ((swapPositions a.castSucc a.succ).subtypeEquiv
    (q := fun p => HasExactExcedances p ((Equiv.swap a.castSucc a.succ) ⁻¹' S))
    (exact_swap_iff a S hl hr))
  let partition := (Equiv.sumCompl fixesRight).symm.trans
    (Equiv.sumCongr right ((Equiv.sumCompl hitsRightFromLeft).symm.trans (Equiv.sumCongr left swapped)))
  have h := Nat.card_congr partition
  change exactCount S =
    Nat.card (ExactPermutations (a.succ.succAbove ⁻¹' S) ⊕
      (ExactPermutations (a.succ.succAbove ⁻¹' (S \ {a.castSucc})) ⊕
        ExactPermutations ((Equiv.swap a.castSucc a.succ) ⁻¹' S))) at h
  rw [Nat.card_sum, Nat.card_sum, delete_swap_set a S hr] at h
  simpa only [exactCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet
