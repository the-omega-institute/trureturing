/- GID: D5/S3/Analytic/Isolation/GoldenGermThirdOrderFourthThresholdRegularity
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermThirdOrderFourthThresholdRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The third golden continuation is regular and negative at one over phi to the fourth. -/

import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity
import D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRealPositivity
import D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign

/- Library-search audit trail (2026-09-03):
   * Exact declaration probes and repository `make lean` confirm the frozen
     public theorems `golden_germ_third_order_factorization`,
     `golden_germ_third_normalized_factor_regularity`,
     `golden_germ_third_normalized_factor_real_axis_positivity`,
     `riemannZeta_ofReal_sign`, and `riemannZeta_ofReal_im_eq_zero`.
   * The factorization theorem exposes its continuation only under
     `ExistsUnique`. Accordingly `thirdContinuation` below reuses that
     theorem's displayed five-zeta formula at the definition level; it does
     not introduce a wrapper pretending that the existential continuation is
     a separately named declaration.
   * Pinned Mathlib supplies `analyticOn_riemannZeta`, `AnalyticAt.comp`,
     `AnalyticAt.inv`, and the golden-ratio identities used to transport the
     five zeta arguments. Real-axis signs come directly from the frozen
     general zeta theorem; no eta argument is rebuilt here. Analyticity and
     positivity of the normalized product come directly from the two frozen
     third-factor theorems.

   STOPPING JUSTIFICATION: this theorem evaluates the explicit third
   continuation only at `1 / phi^4`. It asserts neither O-5 nor the Riemann
   hypothesis, no zero-free complex region, and no all-order extraction. -/

namespace D5.S3.Analytic.Isolation.GoldenGermThirdOrderFourthThresholdRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity
open D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRealPositivity
open D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign

noncomputable section

private noncomputable def a4 : Complex :=
  ((1 / Real.goldenRatio ^ 4 : Real) : Complex)

private noncomputable def thirdG : Complex -> Complex := fun s =>
  ∏' p : Nat.Primes,
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p

private noncomputable def thirdContinuation : Complex -> Complex := fun s =>
  riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
    riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
    (riemannZeta
      (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
    ((riemannZeta
      (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
      riemannZeta
        ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
          Complex) * s)) *
      thirdG s)

private theorem phi_squared_transport :
    ((Real.goldenRatio ^ 2 : Real) : Complex) * a4 =
      ((1 / Real.goldenRatio ^ 2 : Real) : Complex) := by
  rw [a4, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem phi_cubed_transport :
    ((Real.goldenRatio ^ 3 : Real) : Complex) * a4 =
      ((1 / Real.goldenRatio : Real) : Complex) := by
  rw [a4, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem double_phi_squared_transport :
    ((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4 =
      ((2 / Real.goldenRatio ^ 2 : Real) : Complex) := by
  rw [a4, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem double_phi_cubed_transport :
    ((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4 =
      ((2 / Real.goldenRatio : Real) : Complex) := by
  rw [a4, ← Complex.ofReal_mul]
  congr 1
  field_simp [Real.goldenRatio_ne_zero]

private theorem mixed_transport :
    (((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
        Complex) * a4) =
      ((1 + 1 / Real.goldenRatio ^ 2 : Real) : Complex) := by
  rw [a4, ← Complex.ofReal_mul]
  congr 1
  have hsum :
      Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 =
        Real.goldenRatio ^ 4 := by
    calc
      Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 =
          Real.goldenRatio ^ 2 * (1 + Real.goldenRatio) := by ring
      _ = Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 := by
        rw [Real.goldenRatio_sq]
        ring
      _ = Real.goldenRatio ^ 4 := by ring
  rw [show 2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 =
    Real.goldenRatio ^ 4 + Real.goldenRatio ^ 2 by linarith [hsum]]
  field_simp [Real.goldenRatio_ne_zero]

private theorem fifth_threshold_lt_fourth_threshold :
    1 / Real.goldenRatio ^ 5 < 1 / Real.goldenRatio ^ 4 := by
  have hphi4 : 0 < Real.goldenRatio ^ 4 := by positivity
  exact one_div_lt_one_div_of_lt hphi4 (by
    calc
      Real.goldenRatio ^ 4 <
          Real.goldenRatio ^ 4 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi4).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 5 := by ring)

private theorem one_over_phi_squared_pos :
    0 < (1 / Real.goldenRatio ^ 2 : Real) := by positivity

private theorem one_over_phi_squared_lt_one :
    (1 / Real.goldenRatio ^ 2 : Real) < 1 := by
  rw [div_lt_one (by positivity : 0 < Real.goldenRatio ^ 2)]
  nlinarith [Real.one_lt_goldenRatio]

private theorem one_over_phi_pos :
    0 < (1 / Real.goldenRatio : Real) := by positivity

private theorem one_over_phi_lt_one :
    (1 / Real.goldenRatio : Real) < 1 := by
  rw [div_lt_one Real.goldenRatio_pos]
  exact Real.one_lt_goldenRatio

private theorem two_over_phi_squared_pos :
    0 < (2 / Real.goldenRatio ^ 2 : Real) := by positivity

private theorem two_over_phi_squared_lt_one :
    (2 / Real.goldenRatio ^ 2 : Real) < 1 := by
  rw [div_lt_one (by positivity : 0 < Real.goldenRatio ^ 2)]
  rw [Real.goldenRatio_sq]
  linarith [Real.one_lt_goldenRatio]

private theorem one_lt_two_over_phi :
    (1 : Real) < 2 / Real.goldenRatio := by
  exact (lt_div_iff₀ Real.goldenRatio_pos).2 (by
    simpa using Real.goldenRatio_lt_two)

private theorem one_lt_one_plus_one_over_phi_squared :
    (1 : Real) < 1 + 1 / Real.goldenRatio ^ 2 := by
  linarith [one_over_phi_squared_pos]

private theorem zeta_real_negative {x : Real}
    (hx : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : Complex)).im = 0 ∧
      (riemannZeta (x : Complex)).re < 0 := by
  have h := riemannZeta_ofReal_sign hx (ne_of_lt hx1)
  refine ⟨h.1, ?_⟩
  rcases h.2 with hnegative | hpositive
  · exact hnegative.2
  · linarith [hpositive.1]

private theorem zeta_real_positive {x : Real}
    (hx : 1 < x) :
    (riemannZeta (x : Complex)).im = 0 ∧
      0 < (riemannZeta (x : Complex)).re := by
  have h := riemannZeta_ofReal_sign (lt_trans zero_lt_one hx) (ne_of_gt hx)
  refine ⟨h.1, ?_⟩
  rcases h.2 with hnegative | hpositive
  · linarith [hnegative.1]
  · exact hpositive.2

private theorem complex_eq_of_im_eq_zero (z : Complex) (hz : z.im = 0) :
    z = (z.re : Complex) := by
  apply Complex.ext
  · simp
  · simpa using hz

private theorem thirdG_analytic_at_a4 : AnalyticAt Complex thirdG a4 := by
  have hregularity := golden_germ_third_normalized_factor_regularity
  dsimp only at hregularity
  change AnalyticAt Complex (fun s : Complex => ∏' p : Nat.Primes,
    let x := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
    let y := (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
    (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p) a4
  exact hregularity.2.1 a4 (by
    change 1 / Real.goldenRatio ^ 5 < a4.re
    rw [a4, Complex.ofReal_re]
    exact fifth_threshold_lt_fourth_threshold)

private theorem thirdG_ne_zero_at_a4 : thirdG a4 ≠ 0 := by
  have hregularity := golden_germ_third_normalized_factor_regularity
  dsimp only at hregularity
  change thirdG a4 ≠ 0
  exact hregularity.2.2.2.2.2

private theorem thirdG_positive_at_a4 :
    (thirdG a4).im = 0 ∧ 0 < (thirdG a4).re := by
  have hpositive :=
    golden_germ_third_normalized_factor_real_axis_positivity
      (1 / Real.goldenRatio ^ 4) fifth_threshold_lt_fourth_threshold
  dsimp only at hpositive
  change (thirdG a4).im = 0 ∧ 0 < (thirdG a4).re
  exact hpositive

private theorem zeta_phi_squared_ne_zero :
    riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * a4) ≠ 0 := by
  rw [phi_squared_transport]
  have h := zeta_real_negative one_over_phi_squared_pos
    one_over_phi_squared_lt_one
  intro hzero
  rw [hzero, Complex.zero_re] at h
  linarith [h.2]

private theorem zeta_phi_cubed_ne_zero :
    riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * a4) ≠ 0 := by
  rw [phi_cubed_transport]
  have h := zeta_real_negative one_over_phi_pos one_over_phi_lt_one
  intro hzero
  rw [hzero, Complex.zero_re] at h
  linarith [h.2]

private theorem zeta_double_phi_squared_ne_zero :
    riemannZeta (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4) ≠ 0 := by
  rw [double_phi_squared_transport]
  have h := zeta_real_negative two_over_phi_squared_pos
    two_over_phi_squared_lt_one
  intro hzero
  rw [hzero, Complex.zero_re] at h
  linarith [h.2]

private theorem zeta_double_phi_cubed_ne_zero :
    riemannZeta (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4) ≠ 0 := by
  rw [double_phi_cubed_transport]
  apply riemannZeta_ne_zero_of_one_le_re
  change (1 : Real) ≤ 2 / Real.goldenRatio
  exact one_lt_two_over_phi.le

private theorem zeta_mixed_ne_zero :
    riemannZeta
      ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
        Complex) * a4)) ≠ 0 := by
  rw [mixed_transport]
  apply riemannZeta_ne_zero_of_one_le_re
  change (1 : Real) ≤ 1 + 1 / Real.goldenRatio ^ 2
  exact one_lt_one_plus_one_over_phi_squared.le

private theorem zeta_comp_analytic_at_a4 (c : Complex)
    (hc : c * a4 ≠ 1) :
    AnalyticAt Complex (fun s : Complex => riemannZeta (c * s)) a4 := by
  exact (analyticOn_riemannZeta _ hc).comp
    (analyticAt_const.mul analyticAt_id)

private theorem thirdContinuation_analytic_at_a4 :
    AnalyticAt Complex thirdContinuation a4 := by
  have hSq := zeta_comp_analytic_at_a4
    ((Real.goldenRatio ^ 2 : Real) : Complex) (by
      rw [phi_squared_transport]
      exact_mod_cast (ne_of_lt one_over_phi_squared_lt_one))
  have hCub := zeta_comp_analytic_at_a4
    ((Real.goldenRatio ^ 3 : Real) : Complex) (by
      rw [phi_cubed_transport]
      exact_mod_cast (ne_of_lt one_over_phi_lt_one))
  have hDoubleSq := zeta_comp_analytic_at_a4
    ((2 * Real.goldenRatio ^ 2 : Real) : Complex) (by
      rw [double_phi_squared_transport]
      exact_mod_cast (ne_of_lt two_over_phi_squared_lt_one))
  have hDoubleCub := zeta_comp_analytic_at_a4
    ((2 * Real.goldenRatio ^ 3 : Real) : Complex) (by
      rw [double_phi_cubed_transport]
      exact_mod_cast (ne_of_gt one_lt_two_over_phi))
  have hMixed := zeta_comp_analytic_at_a4
    ((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) : Complex) (by
      rw [mixed_transport]
      exact_mod_cast (ne_of_gt one_lt_one_plus_one_over_phi_squared))
  change AnalyticAt Complex
    (fun s : Complex =>
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta
          (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ((riemannZeta
          (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
          riemannZeta
            ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) * thirdG s)) a4
  exact ((hSq.mul hCub).mul
    (hDoubleSq.inv zeta_double_phi_squared_ne_zero)).mul
      ((hDoubleCub.inv zeta_double_phi_cubed_ne_zero).mul hMixed |>.mul
        thirdG_analytic_at_a4)

private theorem thirdContinuation_ne_zero_at_a4 :
    thirdContinuation a4 ≠ 0 := by
  rw [thirdContinuation]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero zeta_phi_squared_ne_zero zeta_phi_cubed_ne_zero)
      (inv_ne_zero zeta_double_phi_squared_ne_zero))
    (mul_ne_zero
      (mul_ne_zero (inv_ne_zero zeta_double_phi_cubed_ne_zero)
        zeta_mixed_ne_zero)
      thirdG_ne_zero_at_a4)

private theorem thirdContinuation_real_negative_at_a4 :
    (thirdContinuation a4).im = 0 ∧
      (thirdContinuation a4).re < 0 := by
  have hSq :
      (riemannZeta
        (((Real.goldenRatio ^ 2 : Real) : Complex) * a4)).im = 0 ∧
      (riemannZeta
        (((Real.goldenRatio ^ 2 : Real) : Complex) * a4)).re < 0 := by
    rw [phi_squared_transport]
    exact zeta_real_negative one_over_phi_squared_pos
      one_over_phi_squared_lt_one
  have hCub :
      (riemannZeta
        (((Real.goldenRatio ^ 3 : Real) : Complex) * a4)).im = 0 ∧
      (riemannZeta
        (((Real.goldenRatio ^ 3 : Real) : Complex) * a4)).re < 0 := by
    rw [phi_cubed_transport]
    exact zeta_real_negative one_over_phi_pos one_over_phi_lt_one
  have hDoubleSq :
      (riemannZeta
        (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4)).im = 0 ∧
      (riemannZeta
        (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4)).re < 0 := by
    rw [double_phi_squared_transport]
    exact zeta_real_negative two_over_phi_squared_pos
      two_over_phi_squared_lt_one
  have hDoubleCub :
      (riemannZeta
        (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4)).im = 0 ∧
      0 < (riemannZeta
        (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4)).re := by
    rw [double_phi_cubed_transport]
    exact zeta_real_positive one_lt_two_over_phi
  have hMixed :
      (riemannZeta
        ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
          Complex) * a4))).im = 0 ∧
      0 < (riemannZeta
        ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
          Complex) * a4))).re := by
    rw [mixed_transport]
    exact zeta_real_positive one_lt_one_plus_one_over_phi_squared
  have hG := thirdG_positive_at_a4
  have hDoubleSqReal := complex_eq_of_im_eq_zero
    (riemannZeta
      (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4)) hDoubleSq.1
  have hDoubleSqInvRe :
      ((riemannZeta
        (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4))⁻¹).re < 0 := by
    rw [hDoubleSqReal, ← Complex.ofReal_inv, Complex.ofReal_re]
    exact inv_neg''.mpr hDoubleSq.2
  have hDoubleSqInvIm :
      ((riemannZeta
        (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4))⁻¹).im = 0 := by
    rw [hDoubleSqReal, ← Complex.ofReal_inv, Complex.ofReal_im]
  have hDoubleCubReal := complex_eq_of_im_eq_zero
    (riemannZeta
      (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4)) hDoubleCub.1
  have hDoubleCubInvRe :
      0 < ((riemannZeta
        (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4))⁻¹).re := by
    rw [hDoubleCubReal, ← Complex.ofReal_inv, Complex.ofReal_re]
    exact inv_pos.mpr hDoubleCub.2
  have hDoubleCubInvIm :
      ((riemannZeta
        (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4))⁻¹).im = 0 := by
    rw [hDoubleCubReal, ← Complex.ofReal_inv, Complex.ofReal_im]
  constructor
  · rw [thirdContinuation]
    simp only [Complex.mul_im, hSq.1, hCub.1, hDoubleSqInvIm,
      hDoubleCubInvIm, hMixed.1, hG.1]
    ring
  · rw [thirdContinuation]
    simp only [Complex.mul_re, Complex.mul_im, hSq.1, hCub.1,
      hDoubleSqInvIm, hDoubleCubInvIm, hMixed.1, hG.1,
      mul_zero, sub_zero, zero_mul, add_zero]
    have hfirst :
        0 < (riemannZeta
          (((Real.goldenRatio ^ 2 : Real) : Complex) * a4)).re *
            (riemannZeta
              (((Real.goldenRatio ^ 3 : Real) : Complex) * a4)).re :=
      mul_pos_of_neg_of_neg hSq.2 hCub.2
    have hleft :
        (riemannZeta
          (((Real.goldenRatio ^ 2 : Real) : Complex) * a4)).re *
            (riemannZeta
              (((Real.goldenRatio ^ 3 : Real) : Complex) * a4)).re *
          ((riemannZeta
            (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * a4))⁻¹).re < 0 :=
      mul_neg_of_pos_of_neg hfirst hDoubleSqInvRe
    have hright :
        0 < ((riemannZeta
          (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * a4))⁻¹).re *
            (riemannZeta
              ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
                Complex) * a4))).re *
          (thirdG a4).re :=
      mul_pos (mul_pos hDoubleCubInvRe hMixed.2) hG.2
    exact mul_neg_of_neg_of_pos hleft hright

/-- The explicit third-order golden continuation is analytic, nonzero, real,
and strictly negative at `1 / phi^4`. -/
theorem golden_germ_third_order_fourth_threshold_regularity :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes, Kp s p
    let F3 : Complex -> Complex := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : Real) : Complex) * s) *
        (riemannZeta
          (((2 * Real.goldenRatio ^ 2 : Real) : Complex) * s))⁻¹ *
        ((riemannZeta
          (((2 * Real.goldenRatio ^ 3 : Real) : Complex) * s))⁻¹ *
          riemannZeta
            ((((2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 : Real) :
              Complex) * s)) *
          G3 s)
    let a4 : Complex := ((1 / Real.goldenRatio ^ 4 : Real) : Complex)
    AnalyticAt Complex F3 a4 ∧
      F3 a4 ≠ 0 ∧
      (F3 a4).im = 0 ∧
      (F3 a4).re < 0 := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  change AnalyticAt Complex thirdContinuation a4 ∧
    thirdContinuation a4 ≠ 0 ∧
    (thirdContinuation a4).im = 0 ∧
    (thirdContinuation a4).re < 0
  exact ⟨thirdContinuation_analytic_at_a4,
    thirdContinuation_ne_zero_at_a4,
    thirdContinuation_real_negative_at_a4⟩

#print axioms golden_germ_third_order_fourth_threshold_regularity

end

end D5.S3.Analytic.Isolation.GoldenGermThirdOrderFourthThresholdRegularity
