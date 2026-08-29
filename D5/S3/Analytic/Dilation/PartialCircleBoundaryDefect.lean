/- GID: D5/S3/Analytic/Dilation/PartialCircleBoundaryDefect
   generality: I
   mirror-B: D5/B/S3/Analytic/Dilation/PartialCircleBoundaryDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A golden-regulator arc accumulates only its endpoint mismatch. -/

import D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity

/- Library-search audit trail (2026-08-29):
   * Current-tree searches for a partial-circle boundary identity, accumulated
     regulator defect, and endpoint ledger found no exact D5 theorem.
   * `GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity` is the canonical
     D5 owner of the exact regulator-period clause and is imported directly.
   * Pinned Mathlib supplies
     `intervalIntegral.integral_eq_sub_of_hasDerivAt`, the exact fundamental
     theorem of calculus needed for the boundary term. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.PartialCircleBoundaryDefect

open scoped goldenRatio Interval

noncomputable section

/-- In a termwise-differentiable convergence region, the accumulated break
field on an oriented regulator arc is exactly the endpoint mismatch of the
golden-unit zeta. An arc of one full regulator period therefore has zero
accumulated break. -/
theorem partial_circle_boundary_defect :
    let sigmaPlus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio
    let sigmaMinus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj
    let anisotropicForm : Real -> Int × Int -> Real := fun eta alpha =>
      Real.exp eta * sigmaPlus alpha ^ 2 +
        Real.exp (-eta) * sigmaMinus alpha ^ 2
    let goldenUnitZeta : Complex -> Real -> Complex := fun s eta =>
      ∑' alpha : {alpha : Int × Int // alpha ≠ 0},
        (anisotropicForm eta alpha : Complex) ^ (-s)
    let goldenBreak : Complex -> Real -> Complex := fun s eta =>
      ∑' alpha : {alpha : Int × Int // alpha ≠ 0},
        ((Real.exp eta * sigmaPlus alpha ^ 2 -
          Real.exp (-eta) * sigmaMinus alpha ^ 2 : Real) : Complex) /
            (anisotropicForm eta alpha : Complex) ^ (s + 1)
    let accumulatedDefect : Complex -> Real -> Real -> Complex := fun s eta0 eta1 =>
      ∫ eta in eta0..eta1, goldenBreak s eta
    ∀ (s : Complex) (eta0 eta1 : Real),
      s ≠ 0 ->
      (∀ eta ∈ Set.uIcc eta0 eta1,
        HasDerivAt (goldenUnitZeta s) (-s * goldenBreak s eta) eta) ->
      IntervalIntegrable (goldenBreak s) MeasureTheory.volume eta0 eta1 ->
      accumulatedDefect s eta0 eta1 =
          -(1 / s) * (goldenUnitZeta s eta1 - goldenUnitZeta s eta0) ∧
        (eta1 - eta0 = 2 * Real.log Real.goldenRatio ->
          accumulatedDefect s eta0 eta1 = 0) := by
  dsimp only
  intro s eta0 eta1 hs hderiv hint
  let sigmaPlus : Int × Int -> Real := fun alpha =>
    (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio
  let sigmaMinus : Int × Int -> Real := fun alpha =>
    (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj
  let anisotropicForm : Real -> Int × Int -> Real := fun eta alpha =>
    Real.exp eta * sigmaPlus alpha ^ 2 +
      Real.exp (-eta) * sigmaMinus alpha ^ 2
  let goldenUnitZeta : Complex -> Real -> Complex := fun s eta =>
    ∑' alpha : {alpha : Int × Int // alpha ≠ 0},
      (anisotropicForm eta alpha : Complex) ^ (-s)
  let goldenBreak : Complex -> Real -> Complex := fun s eta =>
    ∑' alpha : {alpha : Int × Int // alpha ≠ 0},
      ((Real.exp eta * sigmaPlus alpha ^ 2 -
        Real.exp (-eta) * sigmaMinus alpha ^ 2 : Real) : Complex) /
          (anisotropicForm eta alpha : Complex) ^ (s + 1)
  let accumulatedDefect : Complex -> Real -> Real -> Complex := fun s eta0 eta1 =>
    ∫ eta in eta0..eta1, goldenBreak s eta
  change ∀ eta ∈ Set.uIcc eta0 eta1,
    HasDerivAt (goldenUnitZeta s) (-s * goldenBreak s eta) eta at hderiv
  change IntervalIntegrable (goldenBreak s) MeasureTheory.volume eta0 eta1 at hint
  change accumulatedDefect s eta0 eta1 =
      -(1 / s) * (goldenUnitZeta s eta1 - goldenUnitZeta s eta0) ∧
    (eta1 - eta0 = 2 * Real.log Real.goldenRatio ->
      accumulatedDefect s eta0 eta1 = 0)
  have hscaledInt :
      IntervalIntegrable (fun eta => -s * goldenBreak s eta)
        MeasureTheory.volume eta0 eta1 :=
    hint.const_mul (-s)
  have hfund :
      (∫ eta in eta0..eta1, -s * goldenBreak s eta) =
        goldenUnitZeta s eta1 - goldenUnitZeta s eta0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hscaledInt
  have hmul :
      -s * accumulatedDefect s eta0 eta1 =
        goldenUnitZeta s eta1 - goldenUnitZeta s eta0 := by
    simpa only [accumulatedDefect, intervalIntegral.integral_const_mul] using hfund
  have hboundary :
      accumulatedDefect s eta0 eta1 =
        -(1 / s) * (goldenUnitZeta s eta1 - goldenUnitZeta s eta0) := by
    field_simp [hs]
    linear_combination -hmul
  refine ⟨hboundary, ?_⟩
  intro hperiod
  have heta1 : eta1 = eta0 + 2 * Real.log Real.goldenRatio := by
    linarith
  have hperiodic : goldenUnitZeta s eta1 = goldenUnitZeta s eta0 := by
    rw [heta1]
    simpa only [goldenUnitZeta, anisotropicForm, sigmaPlus, sigmaMinus] using
      D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity.golden_unit_zeta_periodicity
        s eta0
  rw [hboundary, hperiodic, sub_self, mul_zero]

#print axioms partial_circle_boundary_defect

end

end D5.S3.Analytic.Dilation.PartialCircleBoundaryDefect
