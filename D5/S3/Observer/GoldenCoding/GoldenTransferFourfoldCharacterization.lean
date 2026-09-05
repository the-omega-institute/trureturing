/- GID: D5/S3/Observer/GoldenCoding/GoldenTransferFourfoldCharacterization
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenTransferFourfoldCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four independent transfer and orbit conditions characterize the golden ratio. -/

import D5.S3.Analytic.Characterizations.GoldenInverseBranchFixedPoint
import D5.S3.Observer.GoldenCoding.GoldenHyperbolicAxis

/-!
Library-search audit trail (2026-09-05): `GoldenTransferTriangle` supplies the sharp disk
radius, reciprocal identity, local derivative, and exponential scale;
`GoldenInverseBranchFixedPoint` supplies the positive fixed-point characterization; and
`GoldenHyperbolicAxis` supplies the trace-three axis length. Repository searches for shortest
closed orbits, geodesic length minimality, and hyperbolic trace minimality found no public theorem
comparing that length with every integral hyperbolic trace. Pinned Mathlib supplies
`Real.arcosh_le_arcosh` and `Real.strictMonoOn_arcosh`, but no combined result. GitHub Lean code
searches for `arcosh` with `trace` and for `closed geodesic` both returned zero hits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.GoldenTransferFourfoldCharacterization

open D5.S3.Analytic.Characterizations.GoldenTransferTriangle
open D5.S3.Analytic.Characterizations.GoldenInverseBranchFixedPoint
open D5.S3.Observer.GoldenCoding.GoldenHyperbolicAxis

private theorem integral_hyperbolic_trace_length_minimal (t : Int)
    (ht : 2 < t.natAbs) :
    goldenAxisTranslationLength ≤
        2 * Real.arcosh ((t.natAbs : Real) / 2) ∧
      (goldenAxisTranslationLength =
          2 * Real.arcosh ((t.natAbs : Real) / 2) ↔
        t.natAbs = 3) := by
  have hthree : 3 ≤ t.natAbs := by omega
  have harg : (3 / 2 : Real) ≤ (t.natAbs : Real) / 2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hthree) (by norm_num)
  have hthreePos : 0 < (3 / 2 : Real) := by norm_num
  have htPos : 0 < (t.natAbs : Real) / 2 := by positivity
  have harcosh : Real.arcosh (3 / 2) ≤
      Real.arcosh ((t.natAbs : Real) / 2) :=
    (Real.arcosh_le_arcosh hthreePos htPos).2 harg
  constructor
  · unfold goldenAxisTranslationLength
    linarith
  · constructor
    · intro hlength
      have heq : Real.arcosh (3 / 2) =
          Real.arcosh ((t.natAbs : Real) / 2) := by
        unfold goldenAxisTranslationLength at hlength
        linarith
      have hinput : (3 / 2 : Real) = (t.natAbs : Real) / 2 :=
        Real.strictMonoOn_arcosh.injOn hthreePos htPos heq
      symm
      exact_mod_cast (show (3 : Real) = t.natAbs by linarith)
    · intro htrace
      simp [goldenAxisTranslationLength, htrace]

private theorem golden_four_conditions_characterize (r : Real) (hr : 1 < r) :
    (IsLUB {s : Real | 1 ≤ s ∧ s < 2 ∧ 1 / (2 - s) < 1 + s} r ↔
        r = Real.goldenRatio) ∧
      ((fun y : Real => 1 / (y + 1)) (r - 1) = r - 1 ↔
        r = Real.goldenRatio) ∧
      (|deriv (fun x : Real => 1 / (x + 1)) (r - 1)| =
          (Real.goldenRatio⁻¹) ^ 2 ↔ r = Real.goldenRatio) ∧
      (Real.exp (-goldenAxisTranslationLength) = (r⁻¹) ^ 4 ↔
        r = Real.goldenRatio) := by
  have htriangle := golden_transfer_triangle
  have hrPos : 0 < r := lt_trans (by norm_num) hr
  have hrNe : r ≠ 0 := ne_of_gt hrPos
  have haxis : goldenAxisTranslationLength =
      4 * Real.log Real.goldenRatio :=
    golden_hyperbolic_axis.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hexpAxis : Real.exp (-goldenAxisTranslationLength) =
      (Real.goldenRatio⁻¹) ^ 4 := by
    rw [haxis]
    exact htriangle.2.2.2
  constructor
  · constructor
    · intro hradius
      exact hradius.unique htriangle.1
    · rintro rfl
      exact htriangle.1
  constructor
  · have hxPos : 0 < r - 1 := by linarith
    rw [golden_inverse_branch_positive_fixed_point_iff (r - 1) hxPos]
    constructor
    · intro hx
      linarith [htriangle.2.1]
    · rintro rfl
      exact htriangle.2.1
  constructor
  · have hderiv :
        deriv (fun x : Real => 1 / (x + 1)) (r - 1) = -(r⁻¹) ^ 2 := by
      have hd := (hasDerivAt_const (𝕜 := Real) (r - 1) 1).div
        ((hasDerivAt_id (𝕜 := Real) (x := r - 1)).add_const 1)
        (by simpa using hrNe)
      convert hd.deriv using 1
      · congr 1
      · simp only [id_eq, sub_add_cancel, zero_mul, one_mul, zero_sub]
        field_simp
    have habs :
        |deriv (fun x : Real => 1 / (x + 1)) (r - 1)| = (r⁻¹) ^ 2 := by
      rw [hderiv, abs_neg, abs_of_nonneg]
      positivity
    rw [habs]
    constructor
    · intro heq
      rw [inv_pow, inv_pow] at heq
      have hsq : r ^ 2 = Real.goldenRatio ^ 2 := inv_injective heq
      nlinarith [Real.goldenRatio_pos]
    · rintro rfl
      rfl
  · rw [hexpAxis]
    constructor
    · intro heq
      rw [inv_pow, inv_pow] at heq
      have hfour : Real.goldenRatio ^ 4 = r ^ 4 := inv_injective heq
      have hfactor :
          (r ^ 2 - Real.goldenRatio ^ 2) *
              (r ^ 2 + Real.goldenRatio ^ 2) = 0 := by
        nlinarith
      have hsum : 0 < r ^ 2 + Real.goldenRatio ^ 2 := by positivity
      have hsq : r ^ 2 = Real.goldenRatio ^ 2 := by
        rcases mul_eq_zero.mp hfactor with hdiff | hzero
        · exact sub_eq_zero.mp hdiff
        · exact False.elim (hsum.ne' hzero)
      nlinarith [Real.goldenRatio_pos]
    · rintro rfl
      rfl

/-- The sharp invariant disk, positive inverse-branch fixed point, local multiplier, and shortest
integral-trace orbit all select the golden ratio. The trace comparison also states that the golden
axis length is attained exactly at absolute trace three. -/
theorem golden_transfer_fourfold_characterization :
    IsLUB {r : Real | 1 ≤ r ∧ r < 2 ∧ 1 / (2 - r) < 1 + r}
        Real.goldenRatio ∧
      Real.goldenRatio - 1 = Real.goldenRatio⁻¹ ∧
      (∀ x : Real, 0 < x →
        ((fun y : Real => 1 / (y + 1)) x = x ↔
          x = Real.goldenRatio⁻¹)) ∧
      |deriv (fun x : Real => 1 / (x + 1))
          (Real.goldenRatio - 1)| = (Real.goldenRatio⁻¹) ^ 2 ∧
      Real.exp (-goldenAxisTranslationLength) =
        (Real.goldenRatio⁻¹) ^ 4 ∧
      (∀ t : Int, 2 < t.natAbs →
        goldenAxisTranslationLength ≤
            2 * Real.arcosh ((t.natAbs : Real) / 2) ∧
          (goldenAxisTranslationLength =
              2 * Real.arcosh ((t.natAbs : Real) / 2) ↔
            t.natAbs = 3)) ∧
      (∀ r : Real, 1 < r →
        (IsLUB {s : Real | 1 ≤ s ∧ s < 2 ∧ 1 / (2 - s) < 1 + s} r ↔
            r = Real.goldenRatio) ∧
          ((fun y : Real => 1 / (y + 1)) (r - 1) = r - 1 ↔
            r = Real.goldenRatio) ∧
          (|deriv (fun x : Real => 1 / (x + 1)) (r - 1)| =
              (Real.goldenRatio⁻¹) ^ 2 ↔ r = Real.goldenRatio) ∧
          (Real.exp (-goldenAxisTranslationLength) = (r⁻¹) ^ 4 ↔
            r = Real.goldenRatio)) := by
  have htriangle := golden_transfer_triangle
  refine ⟨htriangle.1, htriangle.2.1,
    golden_inverse_branch_positive_fixed_point_iff,
    htriangle.2.2.1, ?_, integral_hyperbolic_trace_length_minimal,
    golden_four_conditions_characterize⟩
  have hlength : goldenAxisTranslationLength =
      4 * Real.log Real.goldenRatio :=
    golden_hyperbolic_axis.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hlength]
  exact htriangle.2.2.2

#print axioms golden_transfer_fourfold_characterization

end D5.S3.Observer.GoldenCoding.GoldenTransferFourfoldCharacterization
