/- GID: D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle
   generality: I
   mirror-B: D5/B/S1/FixedPoints/Algebraic/GoldenTransferTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden radius, Gauss fixed point, derivative, and length obey the transfer triangle. -/

import D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Library-search audit trail (2026-08-28):
-- * Exact repository hit `golden_fixed_point_unique` identifies both positive
--   reciprocal fixed points used below; it is imported and applied directly.
-- * Pinned Mathlib provides `Real.inv_goldenRatio`, `Real.goldenRatio_sq`,
--   `HasDerivAt.inv`, `Real.exp_nat_mul`, `Real.exp_neg`, and `Real.exp_log`.
-- * Repository-wide searches found no declaration combining the sharp disk `IsLUB`,
--   Mayer operator origin, and shortest modular-geodesic `IsLeast`. Loogle and GitHub
--   code search found no exact theorem; LeanSearch and Reservoir API routes returned 404.

namespace D5.S1.FixedPoints.Algebraic.GoldenTransferTriangle

open D5.S1.FixedPoints.Algebraic.GoldenFixedPoint
open Set
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The full real Mayer branch family from the source, with no golden parameter.
noncomputable def mayerInverseBranch (n : Nat) (x : Real) : Real :=
  (x + n)⁻¹

-- A concrete real Mayer transfer operator assembled from every branch `n >= 1`.
noncomputable def mayerTransferOperator
    (weight : Nat) (f : Real → Real) (x : Real) : Real :=
  ∑' k : Nat,
    mayerInverseBranch (k + 1) x ^ (2 * weight) *
      f (mayerInverseBranch (k + 1) x)

noncomputable def gaussInverseBranchOne : Real → Real :=
  mayerInverseBranch 1

-- Positive translation lengths of hyperbolic integral trace classes in `PSL₂(ℤ)`.
-- An integer `trace >= 3` is realized by the determinant-one matrix
-- `[[trace, -1], [1, 0]]`, and its closed-geodesic length is characterized by
-- `2 cosh (ell / 2) = trace`.
def modularClosedGeodesicLengths : Set Real :=
  {ell | ∃ trace : Nat,
    3 ≤ trace ∧ 0 < ell ∧ 2 * Real.cosh (ell / 2) = trace}

-- The source theorem with no caller-supplied objects or premises. The witnesses are
-- selected by the maximal disk, the first Mayer branch, and the shortest trace length.
theorem golden_transfer_triangle :
    ∃ rStar xStar ellPhi : Real,
      IsLUB {r : Real | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r} rStar ∧
      rStar = Real.goldenRatio ∧
      xStar = rStar - 1 ∧
      xStar = Real.goldenRatio⁻¹ ∧
      gaussInverseBranchOne xStar = xStar ∧
      |deriv gaussInverseBranchOne xStar| = rStar⁻¹ ^ 2 ∧
      IsLeast modularClosedGeodesicLengths ellPhi ∧
      Real.exp (-ellPhi) = rStar⁻¹ ^ 4 ∧
      (∀ (weight : Nat) (f : Real → Real) (x : Real),
        mayerTransferOperator weight f x =
          ∑' k : Nat,
            mayerInverseBranch (k + 1) x ^ (2 * weight) *
              f (mayerInverseBranch (k + 1) x)) := by
  have hDiskSet :
      {r : Real | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r} =
        Set.Ico 1 Real.goldenRatio := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2, htest⟩
      refine ⟨h1, ?_⟩
      have hden : 0 < 2 - r := by linarith
      rw [div_lt_iff₀ hden] at htest
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    · rintro ⟨h1, hr⟩
      have h2 : r < 2 := hr.trans Real.goldenRatio_lt_two
      refine ⟨h1, h2, ?_⟩
      have hden : 0 < 2 - r := by linarith
      rw [div_lt_iff₀ hden]
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have hDiskMaximal :
      IsLUB {r : Real | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r}
        Real.goldenRatio := by
    rw [hDiskSet]
    exact isLUB_Ico Real.one_lt_goldenRatio
  have hInvGolden : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hShiftGolden : Real.goldenRatio⁻¹ + 1 = Real.goldenRatio := by
    linarith [hInvGolden]
  have hFirstBranchFixed :
      gaussInverseBranchOne Real.goldenRatio⁻¹ = Real.goldenRatio⁻¹ := by
    simpa [gaussInverseBranchOne, mayerInverseBranch] using
      congrArg (fun y : Real => y⁻¹) hShiftGolden
  have hShiftPos : 0 < Real.goldenRatio⁻¹ + 1 := by
    rw [hShiftGolden]
    exact Real.goldenRatio_pos
  have hShiftNe : Real.goldenRatio⁻¹ + 1 ≠ 0 := ne_of_gt hShiftPos
  have hAffine :
      HasDerivAt (fun x : Real => x + 1) 1 Real.goldenRatio⁻¹ :=
    (hasDerivAt_id Real.goldenRatio⁻¹).add_const 1
  have hInverseDerivative := hAffine.inv hShiftNe
  have hGaussBranch :
      gaussInverseBranchOne = (fun x : Real => (x + 1)⁻¹) := by
    funext x
    simp [gaussInverseBranchOne, mayerInverseBranch]
  have hDerivative :
      deriv gaussInverseBranchOne Real.goldenRatio⁻¹ =
        -(Real.goldenRatio⁻¹ + 1)⁻¹ ^ 2 := by
    rw [hGaussBranch]
    change deriv ((fun x : Real => x + 1)⁻¹) Real.goldenRatio⁻¹ = _
    simpa [div_eq_mul_inv, inv_pow] using hInverseDerivative.deriv
  have hDerivativeAbs :
      |deriv gaussInverseBranchOne Real.goldenRatio⁻¹| =
        Real.goldenRatio⁻¹ ^ 2 := by
    rw [hDerivative, abs_neg, abs_pow, abs_inv, abs_of_pos hShiftPos, hShiftGolden]
  have hExpTwoLog :
      Real.exp (2 * Real.log Real.goldenRatio) = Real.goldenRatio ^ 2 := by
    rw [show 2 * Real.log Real.goldenRatio =
      Real.log Real.goldenRatio + Real.log Real.goldenRatio by ring,
      Real.exp_add, Real.exp_log Real.goldenRatio_pos]
    ring
  have hInvGoldenSq :
      (Real.goldenRatio ^ 2)⁻¹ = 2 - Real.goldenRatio := by
    rw [← inv_pow, hInvGolden]
    nlinarith [Real.goldenRatio_sq]
  have hCoshGolden :
      2 * Real.cosh ((4 * Real.log Real.goldenRatio) / 2) = 3 := by
    rw [show (4 * Real.log Real.goldenRatio) / 2 =
      2 * Real.log Real.goldenRatio by ring, Real.cosh_eq, Real.exp_neg, hExpTwoLog]
    rw [hInvGoldenSq]
    nlinarith [Real.goldenRatio_sq]
  have hLogPos : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  have hShortest :
      IsLeast modularClosedGeodesicLengths (4 * Real.log Real.goldenRatio) := by
    constructor
    · exact ⟨3, by norm_num, by positivity, hCoshGolden⟩
    · rintro ell ⟨trace, htrace, hellPos, htraceLength⟩
      have hCoshLe :
          Real.cosh (2 * Real.log Real.goldenRatio) ≤ Real.cosh (ell / 2) := by
        have htraceReal : (3 : Real) ≤ trace := by exact_mod_cast htrace
        have hCoshBase :
            Real.cosh (2 * Real.log Real.goldenRatio) = (3 : Real) / 2 := by
          rw [← show (4 * Real.log Real.goldenRatio) / 2 =
            2 * Real.log Real.goldenRatio by ring]
          linarith [hCoshGolden]
        rw [hCoshBase]
        nlinarith [htraceLength]
      have hAbsLe :
          |2 * Real.log Real.goldenRatio| ≤ |ell / 2| :=
        Real.cosh_le_cosh.mp hCoshLe
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hAbsLe
      linarith
  have hGeodesicExponential :
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
  refine ⟨Real.goldenRatio, Real.goldenRatio⁻¹,
    4 * Real.log Real.goldenRatio, hDiskMaximal, rfl, hInvGolden, rfl,
    hFirstBranchFixed, hDerivativeAbs, hShortest, hGeodesicExponential, ?_⟩
  intro weight f x
  rfl

-- A7 deletion probe: removing the maximal-domain leaf makes this extraction fail.
example :
    IsLUB {r : Real | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r}
      Real.goldenRatio := by
  rcases golden_transfer_triangle with ⟨rStar, xStar, ellPhi, hMaximal, hrStar, _⟩
  simpa [hrStar] using hMaximal

-- A6 deletion probe: removing the exact Mayer-operator leaf makes this extraction fail.
example :
    ∀ (weight : Nat) (f : Real → Real) (x : Real),
      mayerTransferOperator weight f x =
        ∑' k : Nat,
          mayerInverseBranch (k + 1) x ^ (2 * weight) *
            f (mayerInverseBranch (k + 1) x) := by
  rcases golden_transfer_triangle with
    ⟨rStar, xStar, ellPhi, hMaximal, hrStar, hxRadius, hxGolden,
      hFixed, hDerivative, hShortest, hExponential, hOperator⟩
  exact hOperator

-- Countermodel witness: the rejected radius `1 - φ` cannot inhabit the public result.
example :
    ¬ (IsLUB {r : Real | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r}
          (1 - Real.goldenRatio) ∧
        1 - Real.goldenRatio = Real.goldenRatio ∧
        Real.goldenRatio⁻¹ = (1 - Real.goldenRatio) - 1 ∧
        Real.goldenRatio⁻¹ = Real.goldenRatio⁻¹ ∧
        gaussInverseBranchOne Real.goldenRatio⁻¹ = Real.goldenRatio⁻¹ ∧
        |deriv gaussInverseBranchOne Real.goldenRatio⁻¹| =
          (1 - Real.goldenRatio)⁻¹ ^ 2 ∧
        IsLeast modularClosedGeodesicLengths (4 * Real.log Real.goldenRatio) ∧
        Real.exp (-(4 * Real.log Real.goldenRatio)) =
          (1 - Real.goldenRatio)⁻¹ ^ 4) := by
  rintro ⟨_, hRadius, _⟩
  nlinarith [Real.one_lt_goldenRatio]

#print axioms golden_transfer_triangle

end D5.S1.FixedPoints.Algebraic.GoldenTransferTriangle
