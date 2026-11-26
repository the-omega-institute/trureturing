/- GID: D5/S3/Analytic/OriginalHalfBinomialNome
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalHalfBinomialNome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv]
   utility: none
   digest: Entire-disk native nome with exact source normalization and second Taylor coefficient. -/

import D5.S3.Analytic.OriginalHalfBinomialContinuation
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome

/-! The normalized continuation uses the literal original period and its native endpoint. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology

namespace D5.S3.Analytic.OriginalHalfBinomialNome
open OriginalHalfBinomialPeriod (period)
open OriginalHalfBinomialWronskian (tau)
open OriginalHalfBinomialDiskCorrection
open OriginalHalfBinomialContinuation

/-- The native nome extends the whole source-normalized expression across zero. -/
def Q0 (r : ℂ) : ℂ := (r / 16) * Complex.exp (Complex.I * (Real.pi : ℂ) * H r)

private lemma H_derivative {r : ℂ} (hr : r ∈ disk) :
    HasDerivAt H (-Complex.I / (Real.pi : ℂ) * G r) r :=
  disk_correction.2.2.2.2.2.2.2.2.2.1 r hr

private lemma exponent_derivative {r : ℂ} (hr : r ∈ disk) :
    HasDerivAt (fun z => Complex.I * (Real.pi : ℂ) * H z) (G r) r := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  convert (H_derivative hr).const_mul (Complex.I * (Real.pi : ℂ)) using 1
  calc
    G r = -(Complex.I * Complex.I) * G r := by rw [Complex.I_mul_I]; ring
    _ = _ := by field_simp [hpi] <;> ring

private lemma nome_derivative {r : ℂ} (hr : r ∈ disk) :
    HasDerivAt Q0
      (Complex.exp (Complex.I * (Real.pi : ℂ) * H r) * R r / 16) r := by
  have hd := ((hasDerivAt_id r).div_const 16).mul (exponent_derivative hr).cexp
  convert hd using 1
  · funext z
    rfl
  · have hG := disk_correction.2.2.2.2.2.2.2.1 r
    dsimp [Q0]
    linear_combination -(Complex.exp (Complex.I * (Real.pi : ℂ) * H r) / 16) * hG

private lemma lens_norms {r : ℂ} (hr : r ∈ lens) : ‖r‖ < 1 ∧ ‖1 - r‖ < 1 := by
  have hm : r ∈ lens ↔ ‖r‖ < 1 ∧ ‖1 - r‖ < 1 := by
    simp only [lens, mem_inter_iff, Metric.mem_ball, dist_zero_right]
    rw [dist_comm r (1 : ℂ), dist_eq_norm]
  exact hm.mp hr

/-- Full-disk holomorphy, exact derivative, simple zero, and the first two
Taylor coefficients of the actual nome. -/
theorem actual_nome_disk :
    DifferentiableOn ℂ Q0 disk ∧
    (∀ r ∈ disk, HasDerivAt Q0
      (Complex.exp (Complex.I * (Real.pi : ℂ) * H r) /
        (16 * (1 - r) * period r ^ 2)) r) ∧
    (∀ r ∈ disk, deriv Q0 r ≠ 0) ∧
    (∀ r : ℂ, Q0 r = 0 ↔ r = 0) ∧
    deriv Q0 0 = 1 / 16 ∧
    HasDerivAt (deriv Q0) (1 / 16) 0 ∧
    deriv (deriv Q0) 0 / (Nat.factorial 2 : ℂ) = 1 / 32 := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hH0 := disk_correction.2.2.2.2.2.2.2.2.1
  have hR0 := disk_correction.2.2.1
  have hG0 := disk_correction.2.2.2.2.2.2.1
  have hd (r : ℂ) (hr : r ∈ disk) : HasDerivAt Q0
      (Complex.exp (Complex.I * (Real.pi : ℂ) * H r) /
        (16 * (1 - r) * period r ^ 2)) r := by
    convert nome_derivative hr using 1
    simp only [R, div_eq_mul_inv, mul_inv_rev]
    ring
  have hfirst : deriv Q0 0 = 1 / 16 := by
    simpa [hH0, hR0] using (nome_derivative hzero).deriv
  have he : deriv Q0 =ᶠ[𝓝 (0 : ℂ)]
      (fun r => Complex.exp (Complex.I * (Real.pi : ℂ) * H r) * R r / 16) := by
    filter_upwards [Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)] with r hr
    exact (nome_derivative hr).deriv
  have hR : HasDerivAt R (1 / 2) 0 := by
    have hdiff := disk_correction.2.2.2.2.1.differentiableAt
      (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))
    simpa [disk_correction.2.2.2.1] using hdiff.hasDerivAt
  have hsecond : HasDerivAt (deriv Q0) (1 / 16) 0 := by
    convert (((exponent_derivative hzero).cexp.mul hR).div_const 16).congr_of_eventuallyEq he
      using 1
    rw [hH0, hR0, hG0]
    norm_num
  refine ⟨fun r hr => (nome_derivative hr).differentiableAt.differentiableWithinAt,
    hd, ?_, ?_, hfirst, hsecond, ?_⟩
  · intro r hr
    rw [(hd r hr).deriv]
    apply div_ne_zero (Complex.exp_ne_zero _)
    have hp := D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity.period_ne_zero
      (x := r) (by simpa [disk] using hr)
    have h1 : 1 - r ≠ 0 := by
      intro he
      have : r = 1 := (sub_eq_zero.mp he).symm
      simpa [disk, this] using hr
    exact mul_ne_zero (mul_ne_zero (by norm_num) h1) (pow_ne_zero 2 hp)
  · intro r
    simp [Q0, mul_eq_zero, Complex.exp_ne_zero]
  · rw [hsecond.deriv]
    norm_num

/-- On the full lens the nome is the exponential of the literal native ratio;
on the entire positive real unit interval it is the original source nome. -/
theorem actual_nome_source :
    (∀ r ∈ lens, Q0 r = Complex.exp (Complex.I * (Real.pi : ℂ) * tau r)) ∧
    (∀ r : ℝ, 0 < r → r < 1 → Q0 (r : ℂ) =
      (r : ℂ) * Complex.exp (2 *
        D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans.sourceConstant
          (Real.sqrt r : ℂ)) / 16) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hlens (r : ℂ) (hr : r ∈ lens) :
      Q0 r = Complex.exp (Complex.I * (Real.pi : ℂ) * tau r) := by
    rw [← actual_continuation.2 hr]
    have harg : Complex.I * (Real.pi : ℂ) * t0 r =
        Complex.log r - (Real.log 16 : ℂ) + Complex.I * (Real.pi : ℂ) * H r := by
      dsimp [t0]
      field_simp [hpi]
      linear_combination ((Real.log 16 : ℂ) - Complex.log r) * Complex.I_sq
    rw [harg, Complex.exp_add, Complex.exp_sub,
      Complex.exp_log (by
        intro he
        simpa [he] using (lens_norms hr).2),
      ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    rfl
  refine ⟨hlens, ?_⟩
  intro r hr hr1
  have hm : (r : ℂ) ∈ lens := by
    constructor
    · simpa [Metric.mem_ball, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
    · rw [Metric.mem_ball, dist_comm, dist_eq_norm, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < 1 - r by linarith)]
      linarith
  rw [hlens r hm]
  symm
  refine (D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceNome.original_source_nome
    hr hr1).1.trans ?_
  have hp (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
      period (x : ℂ) = ((period (x : ℂ)).re : ℂ) := by
    have hi := (OriginalHalfBinomialIntegral.original_series_eq_integral x hx hx1).2.2
    change period (x : ℂ) = _ at hi
    simp only [hi, Complex.ofReal_re]
  rw [Complex.ofReal_exp]
  congr 1
  rw [tau, hp r hr.le hr1,
    show (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; rfl,
    hp (1 - r) (by linarith) (by linarith)]
  dsimp [D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent.F]
  push_cast
  linear_combination -((Real.pi : ℂ) * (period (1 - (r : ℂ))).re /
    (period (r : ℂ)).re) * Complex.I_sq

end D5.S3.Analytic.OriginalHalfBinomialNome
