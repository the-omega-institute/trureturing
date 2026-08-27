/- GID: D5/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity
   generality: I
   mirror-B: D5/B/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden-unit lattice zeta is periodic along the regulator flow. -/

import Mathlib

namespace D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped goldenRatio

noncomputable section

/-- Multiplication by the fundamental unit reindexes the nonzero coefficient
lattice of `Z[phi]`, so its anisotropic zeta is periodic by twice the
logarithmic regulator. The coefficient pair `(a,b)` represents `a + b*phi`;
the two displayed maps are therefore the two real embeddings of the exact
quadratic-integer carrier. -/
theorem golden_unit_zeta_periodicity :
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
    ∀ (s : Complex) (eta : Real),
      goldenUnitZeta s (eta + 2 * Real.log Real.goldenRatio) =
        goldenUnitZeta s eta := by
  dsimp only
  intro s eta
  let unitMul : Int × Int -> Int × Int := fun alpha =>
    (alpha.2, alpha.1 + alpha.2)
  have unitMul_bijective : Function.Bijective unitMul := by
    constructor
    · intro alpha beta h
      have hSecond : alpha.2 = beta.2 := by
        exact congrArg Prod.fst h
      have hSum : alpha.1 + alpha.2 = beta.1 + beta.2 := by
        exact congrArg Prod.snd h
      apply Prod.ext
      · omega
      · exact hSecond
    · rintro ⟨c, d⟩
      refine ⟨(d - c, c), ?_⟩
      simp [unitMul]
  let shiftPair : Int × Int ≃ Int × Int :=
    Equiv.ofBijective unitMul unitMul_bijective
  have shiftPair_apply (alpha : Int × Int) :
      shiftPair alpha = unitMul alpha := by
    rfl
  have shiftPair_zero : shiftPair (0 : Int × Int) = 0 := by
    rfl
  let shift : {alpha : Int × Int // alpha ≠ 0} ≃
      {alpha : Int × Int // alpha ≠ 0} :=
    shiftPair.subtypeEquiv fun alpha => by
      rw [ne_eq, ne_eq]
      constructor
      · intro hAlpha hShift
        apply hAlpha
        exact shiftPair.injective (hShift.trans shiftPair_zero.symm)
      · intro hShift hAlpha
        apply hShift
        simpa [hAlpha] using shiftPair_zero
  have shift_apply (alpha : {alpha : Int × Int // alpha ≠ 0}) :
      (shift alpha).1 = shiftPair alpha.1 := by
    rfl
  let sigmaPlus : Int × Int -> Real := fun alpha =>
    (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio
  let sigmaMinus : Int × Int -> Real := fun alpha =>
    (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj
  let anisotropicForm : Real -> Int × Int -> Real := fun flow alpha =>
    Real.exp flow * sigmaPlus alpha ^ 2 +
      Real.exp (-flow) * sigmaMinus alpha ^ 2
  let summand : Real -> {alpha : Int × Int // alpha ≠ 0} -> Complex :=
    fun flow alpha => (anisotropicForm flow alpha : Complex) ^ (-s)
  change
    (∑' alpha, summand (eta + 2 * Real.log Real.goldenRatio) alpha) =
      ∑' alpha, summand eta alpha
  have plus_shift (alpha : Int × Int) :
      sigmaPlus (shiftPair alpha) = Real.goldenRatio * sigmaPlus alpha := by
    simp only [sigmaPlus]
    rw [shiftPair_apply]
    simp only [unitMul]
    push_cast
    linear_combination -(alpha.2 : Real) * Real.goldenRatio_sq
  have minus_shift (alpha : Int × Int) :
      sigmaMinus (shiftPair alpha) = Real.goldenConj * sigmaMinus alpha := by
    simp only [sigmaMinus]
    rw [shiftPair_apply]
    simp only [unitMul]
    push_cast
    linear_combination -(alpha.2 : Real) * Real.goldenConj_sq
  have exp_period :
      Real.exp (eta + 2 * Real.log Real.goldenRatio) =
        Real.exp eta * Real.goldenRatio ^ 2 := by
    rw [show 2 * Real.log Real.goldenRatio =
        Real.log Real.goldenRatio + Real.log Real.goldenRatio by ring,
      Real.exp_add, Real.exp_add,
      Real.exp_log Real.goldenRatio_pos]
    ring
  have exp_neg_period :
      Real.exp (-(eta + 2 * Real.log Real.goldenRatio)) =
      Real.exp (-eta) * Real.goldenConj ^ 2 := by
    rw [show -(eta + 2 * Real.log Real.goldenRatio) =
        -eta + (-Real.log Real.goldenRatio + -Real.log Real.goldenRatio) by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
      Real.exp_log Real.goldenRatio_pos, Real.inv_goldenRatio]
    ring
  have form_shift (alpha : Int × Int) :
      anisotropicForm eta (shiftPair alpha) =
        anisotropicForm (eta + 2 * Real.log Real.goldenRatio) alpha := by
    simp only [anisotropicForm]
    rw [plus_shift, minus_shift, exp_period, exp_neg_period]
    ring
  have summand_period (alpha : {alpha : Int × Int // alpha ≠ 0}) :
      summand (eta + 2 * Real.log Real.goldenRatio) alpha =
        summand eta (shift alpha) := by
    simp only [summand]
    rw [shift_apply, form_shift]
  calc
    (∑' alpha, summand (eta + 2 * Real.log Real.goldenRatio) alpha) =
        ∑' alpha, summand eta (shift alpha) := tsum_congr summand_period
    _ = ∑' alpha, summand eta alpha := shift.tsum_eq (summand eta)

#print axioms golden_unit_zeta_periodicity

end

end D5.S3.Analytic.Dilation.GoldenUnitZetaPeriodicity
