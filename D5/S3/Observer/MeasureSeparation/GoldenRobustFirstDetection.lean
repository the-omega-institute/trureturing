/- GID: D5/S3/Observer/MeasureSeparation/GoldenRobustFirstDetection
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/GoldenRobustFirstDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first golden layer below a defect retains uniform normalized energy. -/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

/- Library-search audit trail (2026-09-02):
   * Repository searches for golden first crossings, robust detection, defect energy,
     and the schedule body found no existing owner of this statement.
   * Pinned Mathlib supplies `exists_pow_lt_of_lt_one`, `Nat.find_spec`,
     `Nat.find_min`, and the positivity and lower bound for `Real.goldenRatio`.
   * Local third-party package searches found no theorem combining the minimal
     golden crossing with its normalized energy bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.MeasureSeparation.GoldenRobustFirstDetection

/-- For a defect below the initial one-half layer, the first golden layer crossing the
defect is minimal and its local single-defect energy is at least the fourth inverse
power of the golden ratio. -/
theorem golden_robust_first_detection
    (delta : Real) (deltaPositive : 0 < delta)
    (deltaBelowInitial : delta < (1 / 2 : Real))
    (energy : Real -> Real)
    (singleDefectEnergy : forall omega, 0 < omega -> omega < delta ->
      energy omega = (omega / delta) ^ 2) :
    let layer := fun n : Nat =>
      (1 / 2 : Real) * ((Real.goldenRatio⁻¹) ^ 2) ^ n
    ∃ first : Nat,
      layer first < delta /\
        (∀ n < first, delta <= layer n) /\
          Real.goldenRatio ^ (-4 : Int) <= energy (layer first) := by
  let q : Real := (Real.goldenRatio⁻¹) ^ 2
  let layer := fun n : Nat => (1 / 2 : Real) * q ^ n
  have inversePositive : 0 < Real.goldenRatio⁻¹ :=
    inv_pos.mpr Real.goldenRatio_pos
  have inverseBelowOne : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have qPositive : 0 < q := by
    exact pow_pos inversePositive 2
  have qBelowOne : q < 1 := by
    dsimp [q]
    nlinarith [mul_pos inversePositive (sub_pos.mpr inverseBelowOne)]
  have crossingExists : exists n : Nat, layer n < delta := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (mul_pos (by norm_num : (0 : Real) < 2) deltaPositive) qBelowOne
    refine ⟨n, ?_⟩
    dsimp [layer]
    nlinarith
  let first : Nat := Nat.find crossingExists
  have firstCrosses : layer first < delta := Nat.find_spec crossingExists
  have beforeDoesNotCross (n : Nat) (hn : n < first) : delta <= layer n :=
    le_of_not_gt (Nat.find_min crossingExists hn)
  have firstPositive : 0 < first := by
    apply Nat.pos_of_ne_zero
    intro firstZero
    have initialCrosses : (1 / 2 : Real) < delta := by
      simpa [layer, firstZero] using firstCrosses
    exact (not_lt_of_ge deltaBelowInitial.le) initialCrosses
  have previousBefore : first - 1 < first := Nat.pred_lt firstPositive.ne'
  have previousDoesNotCross : delta <= layer (first - 1) :=
    beforeDoesNotCross (first - 1) previousBefore
  have firstIsNext : first - 1 + 1 = first := Nat.sub_add_cancel firstPositive
  have layerRecurrence : layer first = q * layer (first - 1) := by
    calc
      layer first = layer (first - 1 + 1) := congrArg layer firstIsNext.symm
      _ = q * layer (first - 1) := by
        simp only [layer, pow_succ]
        ring
  have qDeltaBelowFirst : q * delta <= layer first := by
    rw [layerRecurrence]
    exact mul_le_mul_of_nonneg_left previousDoesNotCross qPositive.le
  have layerPositive : 0 < layer first := by
    exact mul_pos (by norm_num) (pow_pos qPositive first)
  have ratioBound : q <= layer first / delta :=
    (le_div_iff₀ deltaPositive).2 qDeltaBelowFirst
  have ratioPositive : 0 < layer first / delta :=
    div_pos layerPositive deltaPositive
  have squareBound : q ^ 2 <= (layer first / delta) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ratioBound)
      (add_nonneg ratioPositive.le qPositive.le)]
  have goldenFourth : Real.goldenRatio ^ (-4 : Int) = q ^ 2 := by
    dsimp [q]
    rw [zpow_neg]
    field_simp [Real.goldenRatio_ne_zero]
  refine ⟨first, firstCrosses, beforeDoesNotCross, ?_⟩
  rw [singleDefectEnergy (layer first) layerPositive firstCrosses, goldenFourth]
  exact squareBound

#print axioms golden_robust_first_detection

end D5.S3.Observer.MeasureSeparation.GoldenRobustFirstDetection
