/- GID: D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle
   generality: I
   mirror-B: D5/B/S1/FixedPoints/Algebraic/GoldenTransferTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden radius, Gauss fixed point, derivative, and length obey the transfer triangle. -/

import D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Library-search audit trail (2026-08-28):
-- * Exact repository hit `golden_fixed_point_unique` identifies both positive
--   reciprocal fixed points used below; it is imported and applied directly.
-- * Pinned Mathlib provides `Real.inv_goldenRatio`, `Real.goldenRatio_sq`,
--   `HasDerivAt.inv`, `Real.exp_nat_mul`, `Real.exp_neg`, and `Real.exp_log`.
-- * Repository-wide searches found no declaration covering the five displayed
--   equality leaves together. Loogle and GitHub code search found no exact
--   combined theorem; the attempted LeanSearch and Reservoir API routes returned 404.

namespace D5.S1.FixedPoints.Algebraic.GoldenTransferTriangle

open D5.S1.FixedPoints.Algebraic.GoldenFixedPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The first real inverse branch of the Gauss map from the source definition.
noncomputable def gaussInverseBranchOne (x : Real) : Real :=
  (x + 1)⁻¹

-- The golden transfer triangle. The hypotheses are precisely the adjacent-source
-- characterizations of the maximal radius, the positive Gauss fixed point, and the
-- golden closed-geodesic length; none is a conclusion leaf restated as a premise.
theorem golden_transfer_triangle
    (rStar xStar ellPhi : Real)
    (hrStarPos : 0 < rStar)
    (hrStarQuadratic : rStar ^ 2 = rStar + 1)
    (hxStarPos : 0 < xStar)
    (hxStarFixed : gaussInverseBranchOne xStar = xStar)
    (hEllPhi : ellPhi = 4 * Real.log Real.goldenRatio) :
    (rStar = Real.goldenRatio ∧
      xStar = rStar - 1 ∧
      xStar = Real.goldenRatio⁻¹ ∧
      |deriv gaussInverseBranchOne xStar| = rStar⁻¹ ^ 2) ∧
      Real.exp (-ellPhi) = rStar⁻¹ ^ 4 := by
  have hrStarNe : rStar ≠ 0 := ne_of_gt hrStarPos
  have hrStarInv : 1 / rStar = rStar - 1 := by
    apply (div_eq_iff hrStarNe).2
    nlinarith [hrStarQuadratic]
  have hrStarReciprocalFixed : goldenReciprocalMap rStar = rStar := by
    rw [goldenReciprocalMap, hrStarInv]
    ring
  have hrStarGoldenRadical : rStar = (1 + Real.sqrt 5) / 2 :=
    ((golden_fixed_point_unique).2.2 rStar hrStarPos).mp hrStarReciprocalFixed
  have hrStarGolden : rStar = Real.goldenRatio := hrStarGoldenRadical
  have hxStarEquation : (xStar + 1)⁻¹ = xStar := by
    simpa [gaussInverseBranchOne] using hxStarFixed
  have hxStarShiftPos : 0 < xStar + 1 := by linarith [hxStarPos]
  have hxStarShiftFixed : goldenReciprocalMap (xStar + 1) = xStar + 1 := by
    simp [goldenReciprocalMap, one_div, hxStarEquation, add_comm]
  have hxStarShiftRadical : xStar + 1 = (1 + Real.sqrt 5) / 2 :=
    ((golden_fixed_point_unique).2.2 (xStar + 1) hxStarShiftPos).mp hxStarShiftFixed
  have hxStarShiftGolden : xStar + 1 = Real.goldenRatio := hxStarShiftRadical
  have hInvGolden : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hxStarGoldenInv : xStar = Real.goldenRatio⁻¹ := by
    linarith [hxStarShiftGolden, hInvGolden]
  have hxStarRadius : xStar = rStar - 1 := by
    linarith [hxStarShiftGolden, hrStarGolden]
  have hxStarShiftNe : xStar + 1 ≠ 0 := ne_of_gt hxStarShiftPos
  have hAffine : HasDerivAt (fun x : Real => x + 1) 1 xStar :=
    (hasDerivAt_id xStar).add_const 1
  have hInverseDerivative := hAffine.inv hxStarShiftNe
  have hDerivative :
      deriv gaussInverseBranchOne xStar = -(xStar + 1)⁻¹ ^ 2 := by
    change deriv ((fun x : Real => x + 1)⁻¹) xStar = _
    simpa [gaussInverseBranchOne, div_eq_mul_inv, inv_pow] using hInverseDerivative.deriv
  have hDerivativeAbs :
      |deriv gaussInverseBranchOne xStar| = rStar⁻¹ ^ 2 := by
    rw [hDerivative, abs_neg, abs_pow, abs_inv, abs_of_pos hxStarShiftPos,
      hxStarShiftGolden, hrStarGolden]
  have hGeodesicExponential : Real.exp (-ellPhi) = rStar⁻¹ ^ 4 := by
    calc
      Real.exp (-ellPhi) = Real.exp (4 * (-Real.log Real.goldenRatio)) := by
        rw [hEllPhi]
        congr 1
        ring
      _ = Real.exp (-Real.log Real.goldenRatio) ^ 4 := by
        simpa using Real.exp_nat_mul (-Real.log Real.goldenRatio) 4
      _ = Real.goldenRatio⁻¹ ^ 4 := by
        rw [Real.exp_neg, Real.exp_log Real.goldenRatio_pos]
      _ = rStar⁻¹ ^ 4 := by rw [hrStarGolden]
  exact ⟨⟨hrStarGolden, hxStarRadius, hxStarGoldenInv, hDerivativeAbs⟩,
    hGeodesicExponential⟩

-- Reverse probe: every public leaf recovers a nontrivial source consequence.
example {rStar xStar ellPhi : Real}
    (h :
      (rStar = Real.goldenRatio ∧
        xStar = rStar - 1 ∧
        xStar = Real.goldenRatio⁻¹ ∧
        |deriv gaussInverseBranchOne xStar| = rStar⁻¹ ^ 2) ∧
        Real.exp (-ellPhi) = rStar⁻¹ ^ 4) :
    rStar ^ 2 = rStar + 1 ∧
      xStar + 1 = rStar ∧
      gaussInverseBranchOne xStar = xStar ∧
      0 < |deriv gaussInverseBranchOne xStar| ∧
      ellPhi = 4 * Real.log Real.goldenRatio := by
  rcases h with ⟨⟨hrStar, hxRadius, hxStar, hDerivative⟩, hExponential⟩
  have hInvGolden : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hShiftGolden : Real.goldenRatio⁻¹ + 1 = Real.goldenRatio := by
    linarith [hInvGolden]
  have hCanonicalExponential :
      Real.exp (-(4 * Real.log Real.goldenRatio)) = Real.goldenRatio⁻¹ ^ 4 := by
    calc
      Real.exp (-(4 * Real.log Real.goldenRatio)) =
          Real.exp (4 * (-Real.log Real.goldenRatio)) := by
        congr 1
        ring
      _ = Real.exp (-Real.log Real.goldenRatio) ^ 4 := by
        simpa using Real.exp_nat_mul (-Real.log Real.goldenRatio) 4
      _ = Real.goldenRatio⁻¹ ^ 4 := by
        rw [Real.exp_neg, Real.exp_log Real.goldenRatio_pos]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hrStar]
    exact Real.goldenRatio_sq
  · linarith [hxRadius]
  · rw [hxStar]
    change (Real.goldenRatio⁻¹ + 1)⁻¹ = Real.goldenRatio⁻¹
    rw [hShiftGolden]
  · rw [hDerivative, hrStar]
    positivity
  · have hExpEq :
        Real.exp (-ellPhi) = Real.exp (-(4 * Real.log Real.goldenRatio)) := by
      rw [hExponential, hrStar]
      exact hCanonicalExponential.symm
    have hNegEq : -ellPhi = -(4 * Real.log Real.goldenRatio) :=
      Real.exp_injective hExpEq
    linarith

-- Carrier-collapse probe: the concrete Gauss branch is not constant.
example : gaussInverseBranchOne 0 ≠ gaussInverseBranchOne 1 := by
  norm_num [gaussInverseBranchOne]

-- Trivialization probes: zero cannot satisfy any of the three source roles.
example : ¬ ((0 : Real) < 0 ∧ (0 : Real) ^ 2 = 0 + 1) := by norm_num

example : ¬ ((0 : Real) < 0 ∧ gaussInverseBranchOne 0 = 0) := by
  norm_num [gaussInverseBranchOne]

example : (0 : Real) ≠ 4 * Real.log Real.goldenRatio := by
  have hLogPos : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  nlinarith

#print axioms golden_transfer_triangle

end D5.S1.FixedPoints.Algebraic.GoldenTransferTriangle
