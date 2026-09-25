/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/PositiveSlots
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/PositiveSlots
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Mandatory labelled slot loads and their exact finite count. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.LabelledWords

/-!
# Mandatory slots

One label is reserved for every required slot.  The remaining load is an
ordinary weak composition, including the empty and infeasible boundaries.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

noncomputable section

/-- Loads of `mass` labels into `r` slots, positive on `required`. -/
def PositiveLoads (r mass : ℕ) (required : Finset (Fin r)) :=
  {loads : Fin r → ℕ //
    (∀ i ∈ required, 0 < loads i) ∧ ∑ i, loads i = mass}

private def requiredUnit {r : ℕ} (required : Finset (Fin r)) (i : Fin r) : ℕ :=
  if i ∈ required then 1 else 0

/-- Removing one reserved label per required slot gives an exact inverse to
adding those labels back.  The right side records the mass equation without
subtraction, so it also covers infeasible parameters. -/
def positiveLoadsEquiv (r mass : ℕ) (required : Finset (Fin r)) :
    PositiveLoads r mass required ≃
      {loads : Fin r → ℕ // (∑ i, loads i) + required.card = mass} where
  toFun loads := ⟨fun i => loads.1 i - requiredUnit required i, by
    have hpoint (i : Fin r) :
        loads.1 i - requiredUnit required i + requiredUnit required i =
          loads.1 i := by
      by_cases hi : i ∈ required
      · simp only [requiredUnit, if_pos hi]
        exact Nat.sub_add_cancel (loads.2.1 i hi)
      · simp [requiredUnit, hi]
    have hsum := congrArg (fun f : Fin r → ℕ => ∑ i, f i) (funext hpoint)
    have hunit : ∑ i, requiredUnit required i = required.card := by
      simpa [requiredUnit] using
        (Finset.card_eq_sum_ite (Finset.subset_univ required)).symm
    simp only [Finset.sum_add_distrib, hunit] at hsum
    exact hsum.trans loads.2.2⟩
  invFun loads := ⟨fun i => loads.1 i + requiredUnit required i, by
    constructor
    · intro i hi
      simp [requiredUnit, hi]
    · have hunit : ∑ i, requiredUnit required i = required.card := by
        simpa [requiredUnit] using
          (Finset.card_eq_sum_ite (Finset.subset_univ required)).symm
      simpa [Finset.sum_add_distrib, hunit] using loads.2⟩
  left_inv loads := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ required
    · simp only [requiredUnit, if_pos hi]
      exact Nat.sub_add_cancel (loads.2.1 i hi)
    · simp [requiredUnit, hi]
  right_inv loads := by
    apply Subtype.ext
    funext i
    simp [Nat.add_sub_cancel]

/-- With enough labels for the mandatory slots, their exact number of load
vectors is the stars-and-bars count of the residual labels. -/
theorem card_positiveLoads_of_le (r mass : ℕ) (required : Finset (Fin r))
    (h : required.card ≤ mass) :
    Nat.card (PositiveLoads r mass required) =
      (r + (mass - required.card) - 1).choose (mass - required.card) := by
  classical
  let remove : PositiveLoads r mass required ≃
      {loads : Fin r → ℕ // ∑ i, loads i = mass - required.card} :=
    (positiveLoadsEquiv r mass required).trans {
      toFun := fun loads => ⟨loads.1, by omega⟩
      invFun := fun loads => ⟨loads.1, by omega⟩
      left_inv := fun loads => Subtype.ext rfl
      right_inv := fun loads => Subtype.ext rfl
    }
  let e := remove.trans (Sym.equivNatSumOfFintype (Fin r)
    (mass - required.card)).symm
  rw [Nat.card_congr e]
  simpa using (Sym.card_sym_eq_choose (α := Fin r) (mass - required.card))

end

end D5.S1.Words.Patterns.ArrowFixedPoint
