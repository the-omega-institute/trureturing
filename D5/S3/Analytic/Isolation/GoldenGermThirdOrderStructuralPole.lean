/- GID: D5/S3/Analytic/Isolation/GoldenGermThirdOrderStructuralPole
   generality: I
   mirror-B: D5/B/S3/Analytic/Isolation/GoldenGermThirdOrderStructuralPole
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The next third-order golden structural pole has an explicit positive residue. -/

import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity
import D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRealPositivity
import D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign
import D5.S3.Analytic.Isolation.GoldenGermStructuralSimplePole
import D5.S3.Analytic.Isolation.GoldenGermSecondOrderStructuralResidue

/- Library-search audit trail (2026-09-03):
   * Exact compile-time probes confirmed the six frozen repository declarations
     imported above. The third factorization exposes its continuation only
     under `ExistsUnique`, so this module reuses its displayed formula at the
     definition level rather than introducing a dead continuation wrapper.
   * `golden_germ_third_normalized_factor_regularity` supplies analyticity of
     `G3`, while
     `golden_germ_third_normalized_factor_real_axis_positivity` supplies its
     real-axis sign. `riemannZeta_ofReal_sign` is used directly for all four
     remaining zeta factors; no eta or sign argument is rebuilt here.
   * The first- and second-pole modules supply the frozen local normal-form and
     residue templates. Pinned Mathlib supplies `riemannZeta_residue_one`,
     `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`, and
     `meromorphicOrderAt_eq_int_iff`.

   STOPPING JUSTIFICATION: this theorem identifies only the next displayed
   third-order structural pole and its positive residue. It asserts no O-5,
   no Riemann hypothesis, no zero-free half-plane, and no all-order extraction. -/

namespace D5.S3.Analytic.Isolation.GoldenGermThirdOrderStructuralPole

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Complex Function
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity
open D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRealPositivity
open D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign
open D5.S3.Analytic.Isolation.GoldenGermStructuralSimplePole
open D5.S3.Analytic.Isolation.GoldenGermSecondOrderStructuralResidue
open scoped Topology

noncomputable section

private noncomputable def zk : ℂ → ℂ := fun s =>
  (s - 1) * riemannZeta s

private noncomputable def zkA : ℂ → ℂ :=
  update zk 1 (limUnder (𝓝[≠] (1 : ℂ)) zk)

private noncomputable def scaleR : ℝ :=
  2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3

private noncomputable def scale : ℂ := (scaleR : ℂ)

private noncomputable def bPt : ℂ := ((1 / scaleR : ℝ) : ℂ)

private noncomputable def phiSq : ℂ :=
  ((Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def phiCub : ℂ :=
  ((Real.goldenRatio ^ 3 : ℝ) : ℂ)

private noncomputable def doublePhiSq : ℂ :=
  ((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ)

private noncomputable def doublePhiCub : ℂ :=
  ((2 * Real.goldenRatio ^ 3 : ℝ) : ℂ)

private noncomputable def thirdG : ℂ → ℂ := fun s =>
  ∏' p : Nat.Primes,
    let x := (p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
    let y := (p : ℂ) ^
      (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
    (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
      (1 - y) * (1 + x)⁻¹ * germLocalFactor s p

private noncomputable def regularMultiplier : ℂ → ℂ := fun s =>
  riemannZeta (phiSq * s) * riemannZeta (phiCub * s) *
    (riemannZeta (doublePhiSq * s))⁻¹ *
      ((riemannZeta (doublePhiCub * s))⁻¹ * thirdG s)

private noncomputable def structuralGerm : ℂ → ℂ := fun s =>
  riemannZeta (scale * s) * regularMultiplier s

private noncomputable def poleResidue : ℂ → ℂ := fun s =>
  zkA (scale * s) * (regularMultiplier s / scale)

private noncomputable def explicitResidue : ℂ :=
  regularMultiplier bPt / scale

private theorem scaleR_pos : 0 < scaleR := by
  rw [scaleR]
  positivity

private theorem scaleR_ne_zero : scaleR ≠ 0 := scaleR_pos.ne'

private theorem scale_ne_zero : scale ≠ 0 := by
  rw [scale]
  exact_mod_cast scaleR_ne_zero

private theorem scaleR_eq_phi_four_plus_phi_sq :
    scaleR = Real.goldenRatio ^ 4 + Real.goldenRatio ^ 2 := by
  have hone_plus_phi :
      1 + Real.goldenRatio = Real.goldenRatio ^ 2 := by
    nlinarith [Real.goldenRatio_sq]
  rw [scaleR]
  calc
    2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3 =
        Real.goldenRatio ^ 2 +
          Real.goldenRatio ^ 2 * (1 + Real.goldenRatio) := by ring
    _ = Real.goldenRatio ^ 2 +
          Real.goldenRatio ^ 2 * Real.goldenRatio ^ 2 := by
      rw [hone_plus_phi]
    _ = Real.goldenRatio ^ 4 + Real.goldenRatio ^ 2 := by ring

private theorem scaleR_lt_phi_fifth :
    scaleR < Real.goldenRatio ^ 5 := by
  have hthree : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hfour : Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
    calc
      Real.goldenRatio ^ 4 =
          Real.goldenRatio * Real.goldenRatio ^ 3 := by ring
      _ = Real.goldenRatio * (2 * Real.goldenRatio + 1) := by
        rw [hthree]
      _ = 3 * Real.goldenRatio + 2 := by
        nlinarith [Real.goldenRatio_sq]
  have hfive : Real.goldenRatio ^ 5 = 5 * Real.goldenRatio + 3 := by
    calc
      Real.goldenRatio ^ 5 =
          Real.goldenRatio ^ 2 * Real.goldenRatio ^ 3 := by ring
      _ = (Real.goldenRatio + 1) *
          (2 * Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq, hthree]
      _ = 5 * Real.goldenRatio + 3 := by
        nlinarith [Real.goldenRatio_sq]
  rw [scaleR_eq_phi_four_plus_phi_sq, hfour,
    Real.goldenRatio_sq, hfive]
  linarith [Real.goldenRatio_pos]

private theorem bPt_in_third_domain :
    1 / Real.goldenRatio ^ 5 < bPt.re := by
  rw [bPt, Complex.ofReal_re]
  exact one_div_lt_one_div_of_lt scaleR_pos scaleR_lt_phi_fifth

private theorem scale_transport : scale * bPt = 1 := by
  rw [scale, bPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [scaleR_ne_zero]

private theorem phiSq_ratio_bounds :
    0 < Real.goldenRatio ^ 2 / scaleR ∧
      Real.goldenRatio ^ 2 / scaleR < 1 := by
  constructor
  · exact div_pos (by positivity) scaleR_pos
  · apply (div_lt_one scaleR_pos).2
    rw [scaleR]
    nlinarith [show 0 < Real.goldenRatio ^ 2 by positivity,
      show 0 < Real.goldenRatio ^ 3 by positivity]

private theorem phiCub_ratio_bounds :
    0 < Real.goldenRatio ^ 3 / scaleR ∧
      Real.goldenRatio ^ 3 / scaleR < 1 := by
  constructor
  · exact div_pos (by positivity) scaleR_pos
  · apply (div_lt_one scaleR_pos).2
    rw [scaleR]
    nlinarith [show 0 < Real.goldenRatio ^ 2 by positivity]

private theorem doublePhiSq_ratio_bounds :
    0 < (2 * Real.goldenRatio ^ 2) / scaleR ∧
      (2 * Real.goldenRatio ^ 2) / scaleR < 1 := by
  constructor
  · exact div_pos (by positivity) scaleR_pos
  · apply (div_lt_one scaleR_pos).2
    rw [scaleR]
    nlinarith [show 0 < Real.goldenRatio ^ 3 by positivity]

private theorem doublePhiCub_ratio_bounds :
    0 < (2 * Real.goldenRatio ^ 3) / scaleR ∧
      (2 * Real.goldenRatio ^ 3) / scaleR < 1 := by
  have hphi3_lt_two_phi2 :
      Real.goldenRatio ^ 3 < 2 * Real.goldenRatio ^ 2 := by
    calc
      Real.goldenRatio ^ 3 =
          Real.goldenRatio ^ 2 * Real.goldenRatio := by ring
      _ < Real.goldenRatio ^ 2 * 2 :=
        mul_lt_mul_of_pos_left Real.goldenRatio_lt_two (by positivity)
      _ = 2 * Real.goldenRatio ^ 2 := by ring
  constructor
  · exact div_pos (by positivity) scaleR_pos
  · apply (div_lt_one scaleR_pos).2
    rw [scaleR]
    linarith

private theorem phiSq_transport :
    phiSq * bPt =
      ((Real.goldenRatio ^ 2 / scaleR : ℝ) : ℂ) := by
  rw [phiSq, bPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [scaleR_ne_zero]

private theorem phiCub_transport :
    phiCub * bPt =
      ((Real.goldenRatio ^ 3 / scaleR : ℝ) : ℂ) := by
  rw [phiCub, bPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [scaleR_ne_zero]

private theorem doublePhiSq_transport :
    doublePhiSq * bPt =
      (((2 * Real.goldenRatio ^ 2) / scaleR : ℝ) : ℂ) := by
  rw [doublePhiSq, bPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [scaleR_ne_zero]

private theorem doublePhiCub_transport :
    doublePhiCub * bPt =
      (((2 * Real.goldenRatio ^ 3) / scaleR : ℝ) : ℂ) := by
  rw [doublePhiCub, bPt, ← Complex.ofReal_mul]
  congr 1
  field_simp [scaleR_ne_zero]

private theorem zeta_negative_between_zero_one {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).im = 0 ∧
      (riemannZeta (x : ℂ)).re < 0 := by
  have hsign := riemannZeta_ofReal_sign hx (ne_of_lt hx1)
  rcases hsign.2 with hnegative | hpositive
  · exact ⟨hsign.1, hnegative.2⟩
  · linarith [hpositive.1]

private theorem zeta_phiSq_sign :
    (riemannZeta (phiSq * bPt)).im = 0 ∧
      (riemannZeta (phiSq * bPt)).re < 0 := by
  rw [phiSq_transport]
  exact zeta_negative_between_zero_one
    phiSq_ratio_bounds.1 phiSq_ratio_bounds.2

private theorem zeta_phiCub_sign :
    (riemannZeta (phiCub * bPt)).im = 0 ∧
      (riemannZeta (phiCub * bPt)).re < 0 := by
  rw [phiCub_transport]
  exact zeta_negative_between_zero_one
    phiCub_ratio_bounds.1 phiCub_ratio_bounds.2

private theorem zeta_doublePhiSq_sign :
    (riemannZeta (doublePhiSq * bPt)).im = 0 ∧
      (riemannZeta (doublePhiSq * bPt)).re < 0 := by
  rw [doublePhiSq_transport]
  exact zeta_negative_between_zero_one
    doublePhiSq_ratio_bounds.1 doublePhiSq_ratio_bounds.2

private theorem zeta_doublePhiCub_sign :
    (riemannZeta (doublePhiCub * bPt)).im = 0 ∧
      (riemannZeta (doublePhiCub * bPt)).re < 0 := by
  rw [doublePhiCub_transport]
  exact zeta_negative_between_zero_one
    doublePhiCub_ratio_bounds.1 doublePhiCub_ratio_bounds.2

private theorem thirdG_analytic : AnalyticAt ℂ thirdG bPt := by
  have hregularity := golden_germ_third_normalized_factor_regularity
  dsimp only at hregularity
  have h := hregularity.2.1 bPt bPt_in_third_domain
  change AnalyticAt ℂ thirdG bPt at h
  exact h

private theorem thirdG_axis_positive :
    (thirdG bPt).im = 0 ∧ 0 < (thirdG bPt).re := by
  have h := golden_germ_third_normalized_factor_real_axis_positivity
    (1 / scaleR) (by
      exact one_div_lt_one_div_of_lt scaleR_pos scaleR_lt_phi_fifth)
  dsimp only at h
  change (thirdG bPt).im = 0 ∧ 0 < (thirdG bPt).re at h
  exact h

private theorem complex_ne_zero_of_re_neg {z : ℂ} (hz : z.re < 0) :
    z ≠ 0 := by
  intro hzero
  rw [hzero, Complex.zero_re] at hz
  exact lt_irrefl 0 hz

private theorem inverse_axis_negative {z : ℂ}
    (him : z.im = 0) (hre : z.re < 0) :
    (z⁻¹).im = 0 ∧ (z⁻¹).re < 0 := by
  have hz : z ≠ 0 := complex_ne_zero_of_re_neg hre
  constructor
  · rw [Complex.inv_im, him]
    simp
  · rw [Complex.inv_re]
    exact div_neg_of_neg_of_pos hre (Complex.normSq_pos.mpr hz)

private theorem mul_axis (z w : ℂ) (hz : z.im = 0) (hw : w.im = 0) :
    (z * w).im = 0 ∧ (z * w).re = z.re * w.re := by
  constructor
  · rw [Complex.mul_im, hz, hw]
    ring
  · rw [Complex.mul_re, hz, hw]
    ring

private theorem regular_axis_positive :
    (regularMultiplier bPt).im = 0 ∧
      0 < (regularMultiplier bPt).re := by
  let z1 : ℂ := riemannZeta (phiSq * bPt)
  let z2 : ℂ := riemannZeta (phiCub * bPt)
  let z3 : ℂ := riemannZeta (doublePhiSq * bPt)
  let z4 : ℂ := riemannZeta (doublePhiCub * bPt)
  have hz1 : z1.im = 0 ∧ z1.re < 0 := by
    simpa [z1] using zeta_phiSq_sign
  have hz2 : z2.im = 0 ∧ z2.re < 0 := by
    simpa [z2] using zeta_phiCub_sign
  have hz3 : z3.im = 0 ∧ z3.re < 0 := by
    simpa [z3] using zeta_doublePhiSq_sign
  have hz4 : z4.im = 0 ∧ z4.re < 0 := by
    simpa [z4] using zeta_doublePhiCub_sign
  have hz3Inv := inverse_axis_negative hz3.1 hz3.2
  have hz4Inv := inverse_axis_negative hz4.1 hz4.2
  have h12 := mul_axis z1 z2 hz1.1 hz2.1
  have h12Pos : 0 < (z1 * z2).re := by
    rw [h12.2]
    exact mul_pos_of_neg_of_neg hz1.2 hz2.2
  have h123 := mul_axis (z1 * z2) z3⁻¹ h12.1 hz3Inv.1
  have h123Neg : (z1 * z2 * z3⁻¹).re < 0 := by
    rw [h123.2]
    exact mul_neg_of_pos_of_neg h12Pos hz3Inv.2
  have h4G := mul_axis z4⁻¹ (thirdG bPt)
    hz4Inv.1 thirdG_axis_positive.1
  have h4GNeg : (z4⁻¹ * thirdG bPt).re < 0 := by
    rw [h4G.2]
    exact mul_neg_of_neg_of_pos hz4Inv.2 thirdG_axis_positive.2
  have hall := mul_axis (z1 * z2 * z3⁻¹) (z4⁻¹ * thirdG bPt)
    h123.1 h4G.1
  have hshape : regularMultiplier bPt =
      (z1 * z2 * z3⁻¹) * (z4⁻¹ * thirdG bPt) := by
    rfl
  constructor
  · rw [hshape]
    exact hall.1
  · rw [hshape, hall.2]
    exact mul_pos_of_neg_of_neg h123Neg h4GNeg

private theorem explicit_residue_axis_positive :
    explicitResidue.im = 0 ∧ 0 < explicitResidue.re := by
  let x : ℝ := (regularMultiplier bPt).re
  have hx : 0 < x := regular_axis_positive.2
  have hregularReal : regularMultiplier bPt = (x : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [x] using regular_axis_positive.1
  have hresidueReal :
      explicitResidue = ((x / scaleR : ℝ) : ℂ) := by
    rw [explicitResidue, hregularReal, scale, Complex.ofReal_div]
  rw [hresidueReal]
  constructor
  · exact Complex.ofReal_im _
  · rw [Complex.ofReal_re]
    exact div_pos hx scaleR_pos

private theorem explicit_residue_ne_zero : explicitResidue ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [Complex.zero_re] at hre
  linarith [explicit_residue_axis_positive.2]

private theorem phiSq_argument_ne_one : phiSq * bPt ≠ 1 := by
  rw [phiSq_transport]
  exact_mod_cast ne_of_lt phiSq_ratio_bounds.2

private theorem phiCub_argument_ne_one : phiCub * bPt ≠ 1 := by
  rw [phiCub_transport]
  exact_mod_cast ne_of_lt phiCub_ratio_bounds.2

private theorem doublePhiSq_argument_ne_one : doublePhiSq * bPt ≠ 1 := by
  rw [doublePhiSq_transport]
  exact_mod_cast ne_of_lt doublePhiSq_ratio_bounds.2

private theorem doublePhiCub_argument_ne_one : doublePhiCub * bPt ≠ 1 := by
  rw [doublePhiCub_transport]
  exact_mod_cast ne_of_lt doublePhiCub_ratio_bounds.2

private theorem zeta_doublePhiSq_ne_zero :
    riemannZeta (doublePhiSq * bPt) ≠ 0 :=
  complex_ne_zero_of_re_neg zeta_doublePhiSq_sign.2

private theorem zeta_doublePhiCub_ne_zero :
    riemannZeta (doublePhiCub * bPt) ≠ 0 :=
  complex_ne_zero_of_re_neg zeta_doublePhiCub_sign.2

private theorem regular_analytic :
    AnalyticAt ℂ regularMultiplier bPt := by
  have hSqOuter : AnalyticAt ℂ riemannZeta (phiSq * bPt) :=
    analyticOn_riemannZeta _ phiSq_argument_ne_one
  have hSqInner : AnalyticAt ℂ (fun s : ℂ => phiSq * s) bPt :=
    analyticAt_const.mul analyticAt_id
  have hCubOuter : AnalyticAt ℂ riemannZeta (phiCub * bPt) :=
    analyticOn_riemannZeta _ phiCub_argument_ne_one
  have hCubInner : AnalyticAt ℂ (fun s : ℂ => phiCub * s) bPt :=
    analyticAt_const.mul analyticAt_id
  have hDoubleSqOuter :
      AnalyticAt ℂ riemannZeta (doublePhiSq * bPt) :=
    analyticOn_riemannZeta _ doublePhiSq_argument_ne_one
  have hDoubleSqInner :
      AnalyticAt ℂ (fun s : ℂ => doublePhiSq * s) bPt :=
    analyticAt_const.mul analyticAt_id
  have hDoubleCubOuter :
      AnalyticAt ℂ riemannZeta (doublePhiCub * bPt) :=
    analyticOn_riemannZeta _ doublePhiCub_argument_ne_one
  have hDoubleCubInner :
      AnalyticAt ℂ (fun s : ℂ => doublePhiCub * s) bPt :=
    analyticAt_const.mul analyticAt_id
  have hSq := hSqOuter.comp hSqInner
  have hCub := hCubOuter.comp hCubInner
  have hDoubleSq := (hDoubleSqOuter.comp hDoubleSqInner).inv
    zeta_doublePhiSq_ne_zero
  have hDoubleCub := (hDoubleCubOuter.comp hDoubleCubInner).inv
    zeta_doublePhiCub_ne_zero
  exact ((hSq.mul hCub).mul hDoubleSq).mul (hDoubleCub.mul thirdG_analytic)

private theorem zkA_at_one : zkA 1 = 1 := by
  rw [zkA, update_self]
  exact riemannZeta_residue_one.limUnder_eq

private theorem zkA_analytic : AnalyticAt ℂ zkA 1 := by
  have hd : DifferentiableOn ℂ zkA (Metric.ball (1 : ℂ) 1) := by
    refine differentiableOn_update_limUnder_of_isLittleO
      (Metric.ball_mem_nhds (1 : ℂ) one_pos) ?_ ?_
    · intro z hz
      exact (((differentiable_id.sub_const 1).differentiableAt).mul
        (differentiableAt_riemannZeta
          (by simpa using hz.2))).differentiableWithinAt
    · exact (((riemannZeta_residue_one.sub_const (zk 1)).norm).isBoundedUnder_le
        ).isLittleO_sub_self_inv
  exact hd.analyticAt (Metric.ball_mem_nhds (1 : ℂ) one_pos)

private theorem pole_residue_analytic : AnalyticAt ℂ poleResidue bPt := by
  have hOuter : AnalyticAt ℂ zkA (scale * bPt) := by
    rw [scale_transport]
    exact zkA_analytic
  have hInner : AnalyticAt ℂ (fun s : ℂ => scale * s) bPt :=
    analyticAt_const.mul analyticAt_id
  exact (hOuter.comp hInner).mul
    (regular_analytic.div analyticAt_const scale_ne_zero)

private theorem pole_residue_ne_zero : poleResidue bPt ≠ 0 := by
  have hvalue : poleResidue bPt = explicitResidue := by
    rw [poleResidue, scale_transport, zkA_at_one, one_mul, explicitResidue]
  rw [hvalue]
  exact explicit_residue_ne_zero

private theorem punctured_normal_form :
    ∀ᶠ s in 𝓝[≠] bPt,
      structuralGerm s = (s - bPt) ^ (-1 : ℤ) • poleResidue s := by
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsb : s - bPt ≠ 0 := sub_ne_zero.mpr hs
  have hne1 : scale * s ≠ 1 := by
    rw [← scale_transport]
    intro hscale
    exact hsb (sub_eq_zero.mpr (mul_left_cancel₀ scale_ne_zero hscale))
  have hzk : zkA (scale * s) =
      (scale * s - 1) * riemannZeta (scale * s) := by
    rw [zkA, update_of_ne hne1, zk]
  have hlinear : scale * s - 1 = scale * (s - bPt) := by
    rw [mul_sub, scale_transport]
  rw [structuralGerm, poleResidue, hzk, hlinear, zpow_neg, zpow_one,
    smul_eq_mul]
  field_simp [scale_ne_zero]

private theorem structural_meromorphic : MeromorphicAt structuralGerm bPt :=
  MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
    ⟨(-1 : ℤ), poleResidue, pole_residue_analytic, punctured_normal_form⟩

private theorem structural_order :
    meromorphicOrderAt structuralGerm bPt = (-1 : ℤ) :=
  (meromorphicOrderAt_eq_int_iff structural_meromorphic).mpr
    ⟨poleResidue, pole_residue_analytic, pole_residue_ne_zero,
      punctured_normal_form⟩

private theorem transported_zeta_residue :
    Tendsto (fun s : ℂ =>
      (scale * s - 1) * riemannZeta (scale * s))
      (𝓝[≠] bPt) (𝓝 1) := by
  have hscale : Tendsto (fun s : ℂ => scale * s)
      (𝓝[≠] bPt) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun s : ℂ => scale * s) :=
        continuous_const.mul continuous_id
      have hcAt : Tendsto (fun s : ℂ => scale * s)
          (𝓝 bPt) (𝓝 1) := by
        have hcT := hc.tendsto bPt
        rw [scale_transport] at hcT
        exact hcT
      exact hcAt.mono_left inf_le_left
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h
      apply hs
      apply mul_left_cancel₀ scale_ne_zero
      rw [h, scale_transport]
  exact riemannZeta_residue_one.comp hscale

private theorem explicit_residue_limit :
    Tendsto (fun s : ℂ => (s - bPt) * structuralGerm s)
      (𝓝[≠] bPt) (𝓝 explicitResidue) := by
  have hregular : Tendsto (fun s : ℂ => regularMultiplier s / scale)
      (𝓝[≠] bPt) (𝓝 (regularMultiplier bPt / scale)) := by
    exact (regular_analytic.continuousAt.tendsto.div_const scale).mono_left
      inf_le_left
  have hproduct := transported_zeta_residue.mul hregular
  have hrewritten :
      Tendsto (fun s : ℂ => (s - bPt) * structuralGerm s)
        (𝓝[≠] bPt) (𝓝 (1 * (regularMultiplier bPt / scale))) := by
    refine hproduct.congr' ?_
    filter_upwards with s
    have hlinear : scale * s - 1 = scale * (s - bPt) := by
      rw [mul_sub, scale_transport]
    rw [structuralGerm, hlinear]
    field_simp [scale_ne_zero]
  simpa only [one_mul, explicitResidue] using hrewritten

/-- Put `B = 2 * phi^2 + phi^3` and `b = 1 / B`. The third-order continued
golden germ has a simple pole at `b`; its explicit residue is the product of
the four regular zeta factors and `G3(b)`, divided by `B`, and is real and
strictly positive. -/
theorem golden_germ_third_order_structural_pole :
    let Kp : ℂ → Nat.Primes → ℂ := fun s p =>
      let x := (p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 2 : ℝ) : ℂ))
      let y := (p : ℂ) ^
        (-s * ((Real.goldenRatio ^ 3 : ℝ) : ℂ))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : ℂ → ℂ := fun s => ∏' p : Nat.Primes, Kp s p
    let B : ℝ := 2 * Real.goldenRatio ^ 2 + Real.goldenRatio ^ 3
    let b : ℂ := ((1 / B : ℝ) : ℂ)
    let regular : ℂ → ℂ := fun s =>
      riemannZeta (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * s) *
        riemannZeta (((Real.goldenRatio ^ 3 : ℝ) : ℂ) * s) *
        (riemannZeta (((2 * Real.goldenRatio ^ 2 : ℝ) : ℂ) * s))⁻¹ *
          ((riemannZeta (((2 * Real.goldenRatio ^ 3 : ℝ) : ℂ) * s))⁻¹ *
            G3 s)
    let F3 : ℂ → ℂ := fun s => riemannZeta ((B : ℂ) * s) * regular s
    let R : ℂ := regular b / (B : ℂ)
    MeromorphicAt F3 b ∧
      meromorphicOrderAt F3 b = (-1 : ℤ) ∧
      Tendsto (fun s : ℂ => (s - b) * F3 s) (𝓝[≠] b) (𝓝 R) ∧
      R.im = 0 ∧ 0 < R.re := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  dsimp only
  change MeromorphicAt structuralGerm bPt ∧
    meromorphicOrderAt structuralGerm bPt = (-1 : ℤ) ∧
    Tendsto (fun s : ℂ => (s - bPt) * structuralGerm s)
      (𝓝[≠] bPt) (𝓝 explicitResidue) ∧
    explicitResidue.im = 0 ∧ 0 < explicitResidue.re
  exact ⟨structural_meromorphic, structural_order, explicit_residue_limit,
    explicit_residue_axis_positive.1, explicit_residue_axis_positive.2⟩

#print axioms golden_germ_third_order_structural_pole

end

end D5.S3.Analytic.Isolation.GoldenGermThirdOrderStructuralPole
