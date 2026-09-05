/- GID: D5/S3/Analytic/GermWindow/GermZeroCertificateJet
   generality: I
   mirror-B: D5/B/S3/Analytic/GermWindow/GermZeroCertificateJet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the golden germ curvature, binary logarithm, and first derivative prefix. -/

import D5.S3.Analytic.GermWindow.GermZeroCertificateReduction

/- Library-search audit trail (2026-09-05):
   * Exact D5 searches on origin/dev found no declaration named
     `g60_curvature_le`, `log_two_binary_60`, or `g1_deriv_re_gt_one`.
     Curvature-shape searches found only the hypotheses in the frozen layer-1
     reduction that this module discharges.
   * Pinned Mathlib exact hits `Real.abs_log_sub_add_sum_range_le`,
     `Real.log_two_gt_d9`, `Real.log_two_lt_d9`, `Real.pi_gt_d20`,
     `Real.pi_lt_d20`, `Real.cos_sub_int_mul_two_pi`, `Real.cos_bound`,
     `Real.exp_bound'`, and `HasDerivAt.const_cpow` supply the analytic
     primitives.  No pinned declaration states any target certificate.
   * D5 exact hits `o5_beta_closed_form` and `o5_beta_power_law` supply the
     frozen golden-exponent identities used by the two content proofs.
   * Exact-name and literal-body searches for `logTwoApprox` found no
     duplicate carrier on origin/dev. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Metric Set
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.GermWindow.GermZeroCertificateReduction

noncomputable section

namespace D5.S3.Analytic.GermWindow.GermZeroCertificateJet

/-- The 60-term rational series used to certify `Real.log 2`. -/
def logTwoApprox : ℚ :=
  ∑ i ∈ Finset.range 60, (2⁻¹ : ℚ) ^ (i + 1) / (i + 1)

private theorem Q_apply :
    Q = Icc (c.re - h) (c.re + h) ×ℂ Icc (c.im - h) (c.im + h) := by
  rw [Q, Rectangle]
  norm_num [h]
  have hh : 0 < h := by norm_num [h]
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]

private theorem beta_nonneg (v : ℕ) : 0 ≤ o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hg := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio := by positivity
      push_cast at hg ⊢
      nlinarith

private theorem beta_lower (v : ℕ) :
    Real.sqrt 5 * (v : ℝ) - 2 / 5 ≤ o5Beta v := by
  have hg := o5_beta_growth v
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_lo : (11 / 5 : ℝ) < Real.sqrt 5 := by nlinarith
  have hinv_lo : (3 / 5 : ℝ) < 1 / Real.goldenRatio := by
    rw [one_div, Real.inv_goldenRatio, Real.goldenConj]
    linarith
  linarith

private theorem beta_upper (v : ℕ) :
    o5Beta v ≤ (9 / 4 : ℝ) * v + 5 / 8 := by
  rw [o5_beta_closed_form, one_div, Real.inv_goldenRatio,
    Real.goldenConj]
  have hfract := Int.fract_nonneg
    (((v + 1 : ℕ) : ℝ) * Real.goldenRatio)
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrt_hi : Real.sqrt 5 < (9 / 4 : ℝ) := by nlinarith
  have hv : (0 : ℝ) ≤ v := by positivity
  nlinarith

private theorem local_term_norm (s : ℂ) (v : ℕ) :
    ‖(2 : ℂ) ^ (-s * (o5Beta v : ℂ))‖ =
      (2 : ℝ) ^ (-s.re * o5Beta v) := by
  change ‖((2 : ℕ) : ℂ) ^ (-s * (o5Beta v : ℂ))‖ = _
  rw [Complex.norm_natCast_cpow_of_pos (by norm_num)]
  simp

private theorem local_term_hasDerivAt (s : ℂ) (v : ℕ) :
    HasDerivAt
      (fun z : ℂ => (2 : ℂ) ^ (-z * (o5Beta v : ℂ)))
      ((2 : ℂ) ^ (-s * (o5Beta v : ℂ)) * Complex.log 2 *
        (-(o5Beta v : ℂ))) s := by
  have he : HasDerivAt (fun z : ℂ => -z * (o5Beta v : ℂ))
      (-(o5Beta v : ℂ)) s :=
    by simpa [id] using
      (hasDerivAt_id s).neg.mul_const (o5Beta v : ℂ)
  simpa only [mul_assoc] using he.const_cpow (c := (2 : ℂ))
    (Or.inl (by norm_num))

private theorem deriv_g (V : ℕ) (s : ℂ) :
    deriv (g V) s =
      ∑ v ∈ Finset.range (V + 1),
        (2 : ℂ) ^ (-s * (o5Beta v : ℂ)) * Complex.log 2 *
          (-(o5Beta v : ℂ)) := by
  unfold g
  exact (HasDerivAt.fun_sum fun v _ => local_term_hasDerivAt s v).deriv

private theorem derivative_mode_re (v : ℕ) :
    (((2 : ℂ) ^ (-c * (o5Beta v : ℂ)) * Complex.log 2 *
      (-(o5Beta v : ℂ))).re) =
      -(Real.log 2 * o5Beta v) *
        Real.exp (-(c.re * o5Beta v * Real.log 2)) *
          Real.cos (c.im * o5Beta v * Real.log 2) := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [Complex.cpow_def_of_ne_zero (by norm_num)]
  rw [hlog]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    Complex.exp_re, Complex.exp_im]
  ring_nf
  rw [Real.cos_neg]

private theorem logTwoApprox_cast :
    (logTwoApprox : ℝ) =
      ∑ i ∈ Finset.range 60,
        (2⁻¹ : ℝ) ^ (i + 1) / (i + 1) := by
  norm_num [logTwoApprox]

/-- The explicit 60-term binary series is within `2⁻⁶⁰` of `Real.log 2`. -/
theorem log_two_binary_60_sum :
    |Real.log 2 -
        (∑ i ∈ Finset.range 60,
          (2⁻¹ : ℝ) ^ (i + 1) / (i + 1))| ≤
      (2⁻¹ : ℝ) ^ 60 := by
  have z := Real.abs_log_sub_add_sum_range_le
    (show |(2⁻¹ : ℝ)| < 1 by norm_num) 60
  rw [show (1 - (2⁻¹ : ℝ)) = 2⁻¹ by norm_num,
    Real.log_inv, ← sub_eq_add_neg, abs_sub_comm] at z
  convert z using 1 <;> norm_num

/-- The named rational approximation is within `2⁻⁶⁰` of `Real.log 2`. -/
theorem log_two_binary_60 :
    |Real.log 2 - (logTwoApprox : ℝ)| ≤ 1 / 2 ^ 60 := by
  rw [logTwoApprox_cast]
  convert log_two_binary_60_sum using 1 <;> norm_num

private theorem beta_one_eq :
    o5Beta 1 = (3 + Real.sqrt 5) / 2 := by
  rw [o5_beta_power_law.1, Real.goldenRatio_sq, Real.goldenRatio]
  ring

private theorem beta_one_bounds :
    (1309 / 500 : ℝ) < o5Beta 1 ∧
      o5Beta 1 < (65451 / 25000 : ℝ) := by
  rw [beta_one_eq]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor <;> nlinarith

private def phaseOne : ℝ := c.im * o5Beta 1 * Real.log 2

private def reducedPhaseOne : ℝ := phaseOne - 3 * Real.pi

private theorem reduced_phase_one_bounds :
    0 < reducedPhaseOne ∧ reducedPhaseOne < (23 / 200 : ℝ) := by
  have hc_lo : (21 / 4 : ℝ) < c.im := by norm_num [c]
  have hc_hi : c.im < (52567123 / 10000000 : ℝ) := by norm_num [c]
  have hb_lo := beta_one_bounds.1
  have hb_hi := beta_one_bounds.2
  have hlog_lo : (693 / 1000 : ℝ) < Real.log 2 :=
    (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlog_hi : Real.log 2 < (693147181 / 1000000000 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hp_lo :
      (21 / 4 : ℝ) * (1309 / 500) * (693 / 1000) < phaseOne := by
    unfold phaseOne
    calc
      (21 / 4 : ℝ) * (1309 / 500) * (693 / 1000) <
          c.im * (1309 / 500) * (693 / 1000) := by gcongr
      _ < c.im * o5Beta 1 * (693 / 1000) := by gcongr
      _ < c.im * o5Beta 1 * Real.log 2 := by gcongr
  have hp_hi : phaseOne <
      (52567123 / 10000000 : ℝ) * (65451 / 25000) *
        (693147181 / 1000000000) := by
    unfold phaseOne
    calc
      c.im * o5Beta 1 * Real.log 2 <
          (52567123 / 10000000 : ℝ) * o5Beta 1 * Real.log 2 := by
        gcongr
      _ < (52567123 / 10000000 : ℝ) * (65451 / 25000) *
          Real.log 2 := by gcongr
      _ < (52567123 / 10000000 : ℝ) * (65451 / 25000) *
          (693147181 / 1000000000) := by gcongr
  have hpi_lo := Real.pi_gt_d20
  have hpi_hi := Real.pi_lt_d20
  unfold reducedPhaseOne
  constructor
  · have : 3 * Real.pi < phaseOne := by
      calc
        3 * Real.pi < 3 * 3.14159265358979323847 := by gcongr
        _ < (21 / 4 : ℝ) * (1309 / 500) * (693 / 1000) := by norm_num
        _ < phaseOne := hp_lo
    linarith
  · have : phaseOne < 3 * Real.pi + (23 / 200 : ℝ) := by
      calc
        phaseOne < (52567123 / 10000000 : ℝ) * (65451 / 25000) *
            (693147181 / 1000000000) := hp_hi
        _ < 3 * 3.14159265358979323846 + (23 / 200 : ℝ) := by
          norm_num
        _ < 3 * Real.pi + (23 / 200 : ℝ) := by gcongr
    linarith

private theorem cos_reduced_phase_one_gt :
    (49 / 50 : ℝ) < Real.cos reducedPhaseOne := by
  have hr := reduced_phase_one_bounds
  have habs : |reducedPhaseOne| ≤ (23 / 200 : ℝ) :=
    abs_le.2 ⟨by linarith, hr.2.le⟩
  have habs_one : |reducedPhaseOne| ≤ 1 := habs.trans (by norm_num)
  have hcos := Real.cos_bound habs_one
  have hlower :
      1 - reducedPhaseOne ^ 2 / 2 -
          |reducedPhaseOne| ^ 4 * (5 / 96) ≤
        Real.cos reducedPhaseOne :=
    sub_le_comm.1 (abs_sub_le_iff.1 hcos).2
  have hsquare : reducedPhaseOne ^ 2 ≤ (23 / 200 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (reducedPhaseOne - 23 / 200),
      sq_nonneg (reducedPhaseOne + 23 / 200)]
  have hfourth : |reducedPhaseOne| ^ 4 ≤ (23 / 200 : ℝ) ^ 4 := by
    gcongr
  calc
    (49 / 50 : ℝ) <
        1 - (23 / 200 : ℝ) ^ 2 / 2 -
          (23 / 200 : ℝ) ^ 4 * (5 / 96) := by norm_num
    _ ≤ 1 - reducedPhaseOne ^ 2 / 2 -
          |reducedPhaseOne| ^ 4 * (5 / 96) := by gcongr
    _ ≤ Real.cos reducedPhaseOne := hlower

private theorem exp_half_lt_five_thirds :
    Real.exp (1 / 2 : ℝ) < 5 / 3 := by
  have hbound := Real.exp_bound'
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℕ) < 5 by norm_num)
  calc
    Real.exp (1 / 2 : ℝ) ≤
        (∑ m ∈ Finset.range 5, (1 / 2 : ℝ) ^ m / m.factorial) +
          (1 / 2 : ℝ) ^ 5 * (5 + 1) / ((5 : ℕ).factorial * 5) :=
      hbound
    _ < 5 / 3 := by norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem decay_one_gt :
    (3 / 5 : ℝ) <
      Real.exp (-(c.re * o5Beta 1 * Real.log 2)) := by
  have hc_pos : 0 < c.re := by norm_num [c]
  have hc_hi : c.re < (1 / 4 : ℝ) := by norm_num [c]
  have hb_pos : 0 < o5Beta 1 := beta_one_bounds.1.trans' (by norm_num)
  have hb_hi := beta_one_bounds.2
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_hi : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hx : c.re * o5Beta 1 * Real.log 2 < (1 / 2 : ℝ) := by
    calc
      c.re * o5Beta 1 * Real.log 2 <
          (1 / 4 : ℝ) * o5Beta 1 * Real.log 2 := by gcongr
      _ < (1 / 4 : ℝ) * (65451 / 25000) * Real.log 2 := by gcongr
      _ < (1 / 4 : ℝ) * (65451 / 25000) * (7 / 10) := by gcongr
      _ < 1 / 2 := by norm_num
  rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  calc
    Real.exp (c.re * o5Beta 1 * Real.log 2) < Real.exp (1 / 2) :=
      Real.exp_strictMono hx
    _ < 5 / 3 := exp_half_lt_five_thirds
    _ = (3 / 5 : ℝ)⁻¹ := by norm_num

/-- The first nonconstant mode already contributes real derivative greater than one. -/
theorem g1_deriv_re_gt_one :
    (1 : ℝ) < (deriv (g 1) c).re := by
  have hder : deriv (g 1) c =
      (2 : ℂ) ^ (-c * (o5Beta 1 : ℂ)) * Complex.log 2 *
        (-(o5Beta 1 : ℂ)) := by
    rw [deriv_g]
    norm_num [Finset.sum_range_succ, o5_beta_zero]
  rw [hder, derivative_mode_re]
  have hphase :
      Real.cos (c.im * o5Beta 1 * Real.log 2) =
        -Real.cos reducedPhaseOne := by
    rw [show c.im * o5Beta 1 * Real.log 2 =
        reducedPhaseOne + 3 * Real.pi by
          simp only [reducedPhaseOne, phaseOne]
          ring]
    rw [show reducedPhaseOne + 3 * Real.pi =
        (reducedPhaseOne + 2 * Real.pi) + Real.pi by ring,
      Real.cos_add_pi, Real.cos_add_two_pi]
  rw [hphase]
  ring_nf
  have hlog : (693 / 1000 : ℝ) < Real.log 2 :=
    (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hb := beta_one_bounds.1
  have he := decay_one_gt
  have he' : (3 / 5 : ℝ) <
      Real.exp (-(Real.log 2 * o5Beta 1 * c.re)) := by
    convert he using 1 <;> ring
  have hcos := cos_reduced_phase_one_gt
  calc
    (1 : ℝ) < (693 / 1000 : ℝ) * (1309 / 500) *
        (3 / 5) * (49 / 50) := by norm_num
    _ < Real.log 2 * o5Beta 1 *
        Real.exp (-(Real.log 2 * o5Beta 1 * c.re)) *
          Real.cos reducedPhaseOne := by gcongr

private theorem second_deriv_g (V : ℕ) (s : ℂ) :
    deriv (deriv (g V)) s =
      ∑ v ∈ Finset.range (V + 1),
        ((2 : ℂ) ^ (-s * (o5Beta v : ℂ)) * Complex.log 2 *
          (-(o5Beta v : ℂ))) * Complex.log 2 *
            (-(o5Beta v : ℂ)) := by
  rw [show deriv (g V) = fun z : ℂ =>
      ∑ v ∈ Finset.range (V + 1),
        (2 : ℂ) ^ (-z * (o5Beta v : ℂ)) * Complex.log 2 *
          (-(o5Beta v : ℂ)) from funext (deriv_g V)]
  exact (HasDerivAt.fun_sum fun v _ =>
    (local_term_hasDerivAt s v).mul_const (Complex.log 2) |>.mul_const
      (-(o5Beta v : ℂ))).deriv

private theorem exp_neg_36911_lt_69139 :
    Real.exp (-(36911 / 100000 : ℝ)) < 69139 / 100000 := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  have hsum := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 36911 / 100000 by norm_num) 5
  calc
    (69139 / 100000 : ℝ)⁻¹ <
        (∑ k ∈ Finset.range 5,
          (36911 / 100000 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (36911 / 100000) := hsum

private theorem exp_0067_lt_107 :
    Real.exp (67 / 1000 : ℝ) < 107 / 100 := by
  have hbound := Real.exp_bound'
    (show (0 : ℝ) ≤ 67 / 1000 by norm_num)
    (show (67 / 1000 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℕ) < 5 by norm_num)
  calc
    Real.exp (67 / 1000 : ℝ) ≤
        (∑ m ∈ Finset.range 5,
          (67 / 1000 : ℝ) ^ m / m.factorial) +
          (67 / 1000 : ℝ) ^ 5 * (5 + 1) /
            ((5 : ℕ).factorial * 5) := hbound
    _ < 107 / 100 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem q_lt :
    (2 : ℝ) ^ (-(c.re - h) * Real.sqrt 5) < 692 / 1000 := by
  have hsigma_pos : 0 < c.re - h := by norm_num [c, h]
  have hsqrt_lo : (2236067977 / 1000000000 : ℝ) < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hsigma_lo : (238153294 / 1000000000 : ℝ) < c.re - h := by
    norm_num [c, h]
  have hsigmasqrt :
      (238153294 / 1000000000 : ℝ) *
          (2236067977 / 1000000000) < (c.re - h) * Real.sqrt 5 := by
    calc
      (238153294 / 1000000000 : ℝ) * (2236067977 / 1000000000) <
          (c.re - h) * (2236067977 / 1000000000) := by
        exact mul_lt_mul_of_pos_right hsigma_lo (by norm_num)
      _ < (c.re - h) * Real.sqrt 5 :=
        mul_lt_mul_of_pos_left hsqrt_lo hsigma_pos
  have hlogprod :
      ((238153294 / 1000000000 : ℝ) *
          (2236067977 / 1000000000)) * (6931471803 / 10000000000) <
        ((c.re - h) * Real.sqrt 5) * Real.log 2 := by
    have hloglo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
      convert Real.log_two_gt_d9 using 1 <;> norm_num
    calc
      ((238153294 / 1000000000 : ℝ) *
          (2236067977 / 1000000000)) * (6931471803 / 10000000000) <
          ((c.re - h) * Real.sqrt 5) * (6931471803 / 10000000000) := by
        exact mul_lt_mul_of_pos_right hsigmasqrt (by norm_num)
      _ < ((c.re - h) * Real.sqrt 5) * Real.log 2 := by
        exact mul_lt_mul_of_pos_left hloglo
          (mul_pos hsigma_pos (Real.sqrt_pos.2 (by norm_num)))
  have ht_lo : (36911 / 100000 : ℝ) <
      (c.re - h) * Real.sqrt 5 * Real.log 2 := by
    exact lt_trans (by norm_num) hlogprod
  calc
    (2 : ℝ) ^ (-(c.re - h) * Real.sqrt 5) =
        Real.exp (-((c.re - h) * Real.sqrt 5 * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring
    _ < Real.exp (-(36911 / 100000 : ℝ)) :=
      Real.exp_strictMono (by linarith)
    _ < 69139 / 100000 := exp_neg_36911_lt_69139
    _ < 692 / 1000 := by norm_num

private theorem B_lt :
    (2 : ℝ) ^ ((c.re - h) * (2 / 5)) < 107 / 100 := by
  have hsigma_pos : 0 < c.re - h := by norm_num [c, h]
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_hi : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hexponent :
      Real.log 2 * ((c.re - h) * (2 / 5)) < 67 / 1000 := by
    calc
      Real.log 2 * ((c.re - h) * (2 / 5)) <
          (7 / 10 : ℝ) * ((c.re - h) * (2 / 5)) := by
        exact mul_lt_mul_of_pos_right hlog_hi (mul_pos hsigma_pos (by norm_num))
      _ < 67 / 1000 := by norm_num [c, h]
  rw [Real.rpow_def_of_pos (by norm_num)]
  exact (Real.exp_strictMono hexponent).trans exp_0067_lt_107

private theorem local_term_geometric_bound {s : ℂ} (hs : s ∈ Q) (v : ℕ) :
    ‖(2 : ℂ) ^ (-s * (o5Beta v : ℂ))‖ ≤
      (107 / 100 : ℝ) * (692 / 1000 : ℝ) ^ v := by
  have hsigma_pos : 0 < c.re - h := by norm_num [c, h]
  have hsigma_le : c.re - h ≤ s.re := by
    rw [Q_apply] at hs
    exact hs.1.1
  have hb := beta_nonneg v
  have hlower := beta_lower v
  rw [local_term_norm]
  calc
    (2 : ℝ) ^ (-s.re * o5Beta v) ≤
        (2 : ℝ) ^ (-(c.re - h) * o5Beta v) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    _ ≤ (2 : ℝ) ^ (-(c.re - h) *
        (Real.sqrt 5 * (v : ℝ) - 2 / 5)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    _ = (2 : ℝ) ^ ((c.re - h) * (2 / 5)) *
        ((2 : ℝ) ^ (-(c.re - h) * Real.sqrt 5)) ^ v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ (107 / 100 : ℝ) * (692 / 1000 : ℝ) ^ v := by
      have hB := B_lt.le
      have hq := q_lt.le
      gcongr

private theorem log_two_norm_le : ‖Complex.log (2 : ℂ)‖ ≤ (7 / 10 : ℝ) := by
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by norm_num))]
  exact Real.log_two_lt_d9.le.trans (by norm_num)

private theorem second_mode_bound {s : ℂ} (hs : s ∈ Q) (v : ℕ) :
    ‖((2 : ℂ) ^ (-s * (o5Beta v : ℂ)) * Complex.log 2 *
          (-(o5Beta v : ℂ))) * Complex.log 2 *
            (-(o5Beta v : ℂ))‖ ≤
      (107 / 100 : ℝ) * (692 / 1000 : ℝ) ^ v *
        (7 / 10) ^ 2 * ((9 / 4 : ℝ) * v + 5 / 8) ^ 2 := by
  have hb0 := beta_nonneg v
  have hbup := beta_upper v
  have hu0 : (0 : ℝ) ≤ (9 / 4 : ℝ) * v + 5 / 8 := by positivity
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_neg, abs_of_nonneg hb0]
  have ht := local_term_geometric_bound hs v
  have hl := log_two_norm_le
  calc
    ‖(2 : ℂ) ^ (-s * (o5Beta v : ℂ))‖ * ‖Complex.log 2‖ *
          o5Beta v * ‖Complex.log 2‖ * o5Beta v ≤
        ((107 / 100 : ℝ) * (692 / 1000 : ℝ) ^ v) *
          (7 / 10) * ((9 / 4 : ℝ) * v + 5 / 8) *
          (7 / 10) * ((9 / 4 : ℝ) * v + 5 / 8) := by
      gcongr
    _ = (107 / 100 : ℝ) * (692 / 1000 : ℝ) ^ v *
        (7 / 10) ^ 2 * ((9 / 4 : ℝ) * v + 5 / 8) ^ 2 := by
      ring

/-- The 61-mode truncation has curvature at most 118 throughout `Q`. -/
theorem g60_curvature_le_118 :
    ∀ s ∈ Q, ‖deriv (deriv (g 60)) s‖ ≤ 118 := by
  intro s hs
  rw [second_deriv_g]
  calc
    ‖∑ v ∈ Finset.range (60 + 1),
        ((2 : ℂ) ^ (-s * (o5Beta v : ℂ)) * Complex.log 2 *
          (-(o5Beta v : ℂ))) * Complex.log 2 *
            (-(o5Beta v : ℂ))‖ ≤
        ∑ v ∈ Finset.range (60 + 1),
          ‖((2 : ℂ) ^ (-s * (o5Beta v : ℂ)) * Complex.log 2 *
            (-(o5Beta v : ℂ))) * Complex.log 2 *
              (-(o5Beta v : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ Finset.range (60 + 1),
        (107 / 100 : ℝ) * (692 / 1000 : ℝ) ^ v *
          (7 / 10) ^ 2 * ((9 / 4 : ℝ) * v + 5 / 8) ^ 2 := by
      exact Finset.sum_le_sum fun v _ => second_mode_bound hs v
    _ ≤ 118 := by
      norm_num [Finset.sum_range_succ]

/-- The layer-1 curvature hypothesis holds unconditionally throughout `Q`. -/
theorem g60_curvature_le :
    ∀ s ∈ Q, ‖deriv (deriv (g 60)) s‖ ≤ 400 := by
  intro s hs
  exact (g60_curvature_le_118 s hs).trans (by norm_num)

example : c ∈ Q := c_mem_Q

example : Nonempty {s : ℂ // s ∈ Q} := ⟨⟨c, c_mem_Q⟩⟩

#print axioms log_two_binary_60
#print axioms log_two_binary_60_sum
#print axioms g1_deriv_re_gt_one
#print axioms g60_curvature_le_118
#print axioms g60_curvature_le

end D5.S3.Analytic.GermWindow.GermZeroCertificateJet
