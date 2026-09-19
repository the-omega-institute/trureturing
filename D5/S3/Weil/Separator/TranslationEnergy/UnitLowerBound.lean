/- GID: D5/S3/Weil/Separator/TranslationEnergy/UnitLowerBound
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/UnitLowerBound
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: none
   digest: Lower-bound the full translation energy of the unit literal Weil test. -/

import D5.S3.Weil.Separator.TranslationEnergy.Integral
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Separator.TranslationEnergy.UnitLowerBound

open Set MeasureTheory Polynomial
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation
open D5.S3.Weil.Separator.TranslationEnergy.LiteralFunction
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

/-- The radius-one literal test with both rational polynomials equal to one. -/
def unitLiteral : WeilTestFunction :=
  literalRationalTest 1 (by omega) (C 1) (C 1)

/-- Every shift from `5 / 8` through `1` separates a fixed interval of the
unit literal plateau from at least half of the translated cutoff. -/
theorem unit_literal_translationEnergy_lower (s : Real)
    (hsLower : (5 / 8 : Real) ≤ s) (hsUpper : s ≤ 1) :
    (1 / 16 : Real) ≤ translationEnergy unitLiteral s := by
  let F : Real -> Real := fun y => Complex.normSq (unitLiteral y - unitLiteral (y - s))
  have hunit (x : Real) :
      unitLiteral x =
        ((Real.smoothTransition (2 - |x|) : Real) : Complex) * (1 + Complex.I) := by
    change (literalRationalTest 1 (by omega) (C 1) (C 1)).toFun x = _
    simp [literalRationalTest, rationalEvenPolynomial]
  have hhalf : Real.smoothTransition (1 / 2 : Real) = 1 / 2 := by
    rw [Real.smoothTransition]
    rw [show (1 : Real) - 1 / 2 = 1 / 2 by norm_num]
    have hne : expNegInvGlue (1 / 2 : Real) ≠ 0 :=
      ne_of_gt (expNegInvGlue.pos_of_pos (by norm_num))
    field_simp [hne]
    norm_num
  have hpoint : ∀ y ∈ Icc (-1 : Real) (-7 / 8 : Real), (1 / 2 : Real) ≤ F y := by
    intro y hy
    have hyNeg : y < 0 := by linarith [hy.2]
    have hyShiftNeg : y - s < 0 := by linarith [hy.2, hsLower]
    have hcutY : Real.smoothTransition (2 - |y|) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [abs_of_neg hyNeg]; linarith [hy.1])
    have hargShift : 2 - |y - s| ≤ (1 / 2 : Real) := by
      rw [abs_of_neg hyShiftNeg]
      linarith [hy.2, hsLower]
    have hargShiftNonneg : 0 ≤ 2 - |y - s| := by
      rw [abs_of_neg hyShiftNeg]
      linarith [hy.1, hsUpper]
    have hcutShift : Real.smoothTransition (2 - |y - s|) ≤ (1 / 2 : Real) := by
      calc
        Real.smoothTransition (2 - |y - s|) ≤ Real.smoothTransition (1 / 2) :=
          Real.smoothTransition.monotone hargShift
        _ = 1 / 2 := hhalf
    have hcutShiftNonneg : 0 ≤ Real.smoothTransition (2 - |y - s|) := by
      calc
        0 = Real.smoothTransition 0 := Real.smoothTransition.zero.symm
        _ ≤ Real.smoothTransition (2 - |y - s|) :=
          Real.smoothTransition.monotone hargShiftNonneg
    have hnorm : F y =
        2 * (1 - Real.smoothTransition (2 - |y - s|)) ^ 2 := by
      dsimp [F]
      rw [hunit y, hunit (y - s), hcutY]
      simp only [Complex.ofReal_one, one_mul, Complex.normSq_apply]
      simp
      ring
    rw [hnorm]
    nlinarith [sq_nonneg (Real.smoothTransition (2 - |y - s|) - 1 / 2)]
  have hcontinuous : Continuous F := by
    dsimp [F]
    exact Complex.continuous_normSq.comp
      (unitLiteral.continuous.sub
        (unitLiteral.continuous.comp (continuous_id.sub continuous_const)))
  have hshiftCompact : HasCompactSupport (fun y : Real => unitLiteral (y - s)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using
      unitLiteral.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-s))
  have hcompact : HasCompactSupport F := by
    exact (unitLiteral.hasCompactSupport.sub hshiftCompact).comp_left (by simp)
  have hFint : Integrable F := hcontinuous.integrable_of_hasCompactSupport hcompact
  have hrestrict :
      (∫ y in Icc (-1 : Real) (-7 / 8 : Real), F y) ≤ ∫ y : Real, F y :=
    setIntegral_le_integral hFint (ae_of_all _ fun y => Complex.normSq_nonneg _)
  have hmeasure : volume.real (Icc (-1 : Real) (-7 / 8 : Real)) = 1 / 8 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
    · norm_num
    · norm_num
  have hlocal :
      (1 / 2 : Real) * volume.real (Icc (-1 : Real) (-7 / 8 : Real)) ≤
        ∫ y in Icc (-1 : Real) (-7 / 8 : Real), F y :=
    setIntegral_ge_of_const_le_real measurableSet_Icc measure_Icc_lt_top.ne hpoint
      hFint.integrableOn
  rw [hmeasure] at hlocal
  rw [translationEnergy]
  change (1 / 16 : Real) ≤ ∫ y : Real, F y
  nlinarith [hlocal.trans hrestrict]

#print axioms unit_literal_translationEnergy_lower

end D5.S3.Weil.Separator.TranslationEnergy.UnitLowerBound
