/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGeneratedSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual signed two-mode displacement sums with polynomial zero-mode boundaries. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums

/-! Negative mode equations are multiplied by the mode variable before summation. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
open OriginalGaussianSourceEvaluation OriginalGaussianExternalFrequency
open OriginalGaussianExternalDisplacement OriginalGaussianExternalMoments
open OriginalGaussianExternalGenerators OriginalGaussianExternalModeSums
open OriginalGaussianExternalSourceJet OriginalGaussianExternalNormal
open OriginalGaussianExternalJetSums OriginalGaussianExternalEvolution
open OriginalGaussianExternalResolvent

/-- The multiplier removes the negative-label Laurent denominator. -/
def modeScale (out : Bool) (u : ℂ) : ℂ := if out then 1 else u

/-- The scaled signed U amplitude is regular at the input-zero boundary. -/
def modeA (out : Bool) (u x : ℂ) : ℂ :=
  if out then (1 - 2 * u + (1 - x) * u ^ 2) / (2 * (1 - (1 - x) * u))
  else u * (1 - u) / (2 * (1 - x - u)) - 1 / 2

/-- Both scaled source-boundary coefficients are constants. -/
def modeB (out : Bool) : ℂ := if out then 1 / 2 else -1 / 2

/-- The scaled diagonal jet amplitude includes the actual period logarithmic derivative. -/
def modeH (out : Bool) (u x lambdaRatio : ℂ) : ℂ :=
  (if out then -x * u / (1 - (1 - x) * u) else x * u / (1 - x - u)) -
    modeA out u x - 2 * x * modeScale out u * lambdaRatio

private lemma moment_sums (out : Bool) {u : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ‖u‖ + r < 1) :
    let x : ℂ := r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    HasSum (fun p : ℕ => modeScale out u * sourceMoment out p x * u ^ p)
      (sourceMode out u x * modeA out u x - modeB out * sourceAmplitude false 0 x) ∧
    HasSum (fun p : ℕ => modeScale out u * sourceJetMoment out p x * u ^ p)
      (sourceMode out u x * modeH out u x lambdaRatio + modeB out * sourceAmplitude false 0 x) := by
  have hs : ‖u‖ + ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hu
  have hU := sourceMoment_generators_explicit hs
  have hV := sourceJetMoment_generators_explicit hr hr1 hu
  dsimp only at hV ⊢
  cases out
  · constructor
    · convert hU.2 using 1 <;> simp only [modeScale, modeA, modeB,
        Bool.false_eq_true, ite_false]
      ring
    · convert hV.2 using 1 <;> simp only [modeScale, modeA, modeB, modeH,
        Bool.false_eq_true, ite_false]
      ring
  · constructor
    · convert hU.1 using 1 <;> simp only [modeScale, modeA, modeB, ite_true, one_mul]
      ring
    · convert hV.1 using 1 <;> simp only [modeScale, modeA, modeB, modeH,
        ite_true, one_mul]
      ring

set_option maxHeartbeats 800000 in
-- The two full product-series elaborations include all signed source telescopes.
/-- Both complete literal displacement equations sum to the explicit signed U/V products. -/
theorem external_displacement_generated (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ‖u‖ + r < 1) (hv : ‖v‖ + r < 1) :
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    let U := fun e w => sourceMode e w x * modeA e w x -
      modeB e * sourceAmplitude false 0 x
    let V := fun e w => sourceMode e w x * modeH e w x lambdaRatio +
      modeB e * sourceAmplitude false 0 x
    HasSum (fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
      (modeFrequency out pq.1 (fun e k => externalJ e k out' pq.2 z) +
        modeFrequency out' pq.2 (fun e k => externalJ out pq.1 e k z)) *
          u ^ pq.1 * v ^ pq.2)
      ((1 - x) * (U out u * V out' v + V out u * U out' v) / 2) ∧
    HasSum (fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
      (modeFrequency out pq.1 (fun e k => externalT e k out' pq.2 z) -
        modeFrequency out' pq.2 (fun e k => externalT out pq.1 e k z)) *
          u ^ pq.1 * v ^ pq.2)
      ((1 - x) * (U out u * V out' v - V out u * U out' v) / 2) := by
  have hL := moment_sums out hr hr1 hu
  have hR := moment_sums out' hr hr1 hv
  dsimp only at hL hR ⊢
  have hUV := hL.1.mul hR.2
    (summable_mul_of_summable_norm
      (f := fun p : ℕ => modeScale out u * sourceMoment out p r * u ^ p)
      (g := fun q : ℕ => modeScale out' v * sourceJetMoment out' q r * v ^ q)
      hL.1.summable.norm hR.2.summable.norm)
  have hVU := hL.2.mul hR.1
    (summable_mul_of_summable_norm
      (f := fun p : ℕ => modeScale out u * sourceJetMoment out p r * u ^ p)
      (g := fun q : ℕ => modeScale out' v * sourceMoment out' q r * v ^ q)
      hL.2.summable.norm hR.1.summable.norm)
  constructor
  · have hh := (hUV.add hVU).mul_left ((1 - (r : ℂ)) / 2)
    rw [div_mul_eq_mul_div] at hh
    apply hh.congr_fun
    intro pq
    have hx : ‖(r : ℂ)‖ < 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
    have hsource := external_source_equations out pq.1 out' pq.2 hr hr1
    dsimp only at hsource
    rw [hsource.1]
    simp only [sourceJetMoment_eq_derivative _ _ hr hr1,
      sourceMoment_eq_modeFrequency _ _ hx]
    ring
  · have hh := (hUV.sub hVU).mul_left ((1 - (r : ℂ)) / 2)
    rw [div_mul_eq_mul_div] at hh
    apply hh.congr_fun
    intro pq
    have hx : ‖(r : ℂ)‖ < 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
    have hsource := external_source_equations out pq.1 out' pq.2 hr hr1
    dsimp only at hsource
    rw [hsource.2.1]
    simp only [sourceJetMoment_eq_derivative _ _ hr hr1,
      sourceMoment_eq_modeFrequency _ _ hx]
    ring

set_option maxHeartbeats 800000 in
-- The full tensor product of the two diagonal jet series is elaborated here.
/-- The full literal T radial remainder sums to the explicit signed V/V minus U/U product. -/
theorem external_radial_generated (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ‖u‖ + r < 1) (hv : ‖v‖ + r < 1) :
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    let U := fun e w => sourceMode e w x * modeA e w x -
      modeB e * sourceAmplitude false 0 x
    let V := fun e w => sourceMode e w x * modeH e w x lambdaRatio +
      modeB e * sourceAmplitude false 0 x
    HasSum (fun pq : ℕ × ℕ => modeScale out u * modeScale out' v *
      (2 * x * deriv (fun t : ℝ => externalT out pq.1 out' pq.2 (Real.sqrt t : ℂ)) r -
        modeFrequency out pq.1 (fun e k => externalT e k out' pq.2 z) -
        modeFrequency out' pq.2 (fun e k => externalT out pq.1 e k z)) *
          u ^ pq.1 * v ^ pq.2)
      ((1 - x) * (V out u * V out' v - U out u * U out' v) / 2) := by
  have hL := moment_sums out hr hr1 hu
  have hR := moment_sums out' hr hr1 hv
  dsimp only at hL hR ⊢
  have hVV := hL.2.mul hR.2
    (summable_mul_of_summable_norm
      (f := fun p : ℕ => modeScale out u * sourceJetMoment out p r * u ^ p)
      (g := fun q : ℕ => modeScale out' v * sourceJetMoment out' q r * v ^ q)
      hL.2.summable.norm hR.2.summable.norm)
  have hUU := hL.1.mul hR.1
    (summable_mul_of_summable_norm
      (f := fun p : ℕ => modeScale out u * sourceMoment out p r * u ^ p)
      (g := fun q : ℕ => modeScale out' v * sourceMoment out' q r * v ^ q)
      hL.1.summable.norm hR.1.summable.norm)
  have hh := (hVV.sub hUU).mul_left ((1 - (r : ℂ)) / 2)
  rw [div_mul_eq_mul_div] at hh
  apply hh.congr_fun
  intro pq
  rw [(externalT_radial_equation out pq.1 out' pq.2 hr hr1).deriv]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hr0]
  ring

lemma boundary_normalization {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (Real.sqrt (1 - r) : ℂ) * sourceAmplitude false 0 r = 1 := by
  have hs : ‖(0 : ℂ)‖ + ‖(r : ℂ)‖ < 1 := by
    simpa only [norm_zero, zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      using hr1
  have he : sourceAmplitude false 0 r = (1 - (r : ℂ)) ^ (-1 / 2 : ℂ) := by
    have hh := (sourceAmplitude_generators hs).2.tsum_eq
    have hz : (fun p : ℕ => sourceAmplitude false p (r : ℂ) * (0 : ℂ) ^ p) =
        Pi.single 0 (sourceAmplitude false 0 r) := by
      funext p
      cases p <;> simp
    rw [hz, tsum_pi_single] at hh
    simpa only [sub_zero, div_one, one_div_one, one_mul] using hh
  rw [he]
  have hc : 0 < 1 - r := by linarith
  have hp : (1 - (r : ℂ)) ^ (-1 / 2 : ℂ) = ((1 - r : ℝ) ^ (-1 / 2 : ℝ) : ℝ) := by
    convert (Complex.ofReal_cpow hc.le (-1 / 2 : ℝ)).symm using 1 <;> push_cast <;> ring
  rw [hp, ← Complex.ofReal_mul]
  change ((Real.sqrt (1 - r) * (1 - r) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ)
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hc]
  norm_num

/-- Both genuine negative-zero rows are evaluated by the same signed source amplitudes. -/
theorem external_negative_zero_generated (out : Bool) {u : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ‖u‖ + r < 1) :
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    HasSum (fun p : ℕ => modeScale out u * externalJ false 0 out p z * u ^ p)
      ((Real.sqrt (1 - r) : ℂ) / 2 *
        (sourceMode out u x * (modeH out u x lambdaRatio - modeA out u x)) + modeB out) ∧
    HasSum (fun p : ℕ => modeScale out u * externalT false 0 out p z * u ^ p)
      ((Real.sqrt (1 - r) : ℂ) / 2 *
        (sourceMode out u x * (modeH out u x lambdaRatio + modeA out u x))) := by
  have h := moment_sums out hr hr1 hu
  dsimp only at h ⊢
  constructor
  · have hh := (h.2.sub h.1).mul_left ((Real.sqrt (1 - r) : ℂ) / 2)
    convert hh using 1
    · ext p
      rw [(external_negative_zero_boundary out p hr hr1).1]
      ring
    · have hn := boundary_normalization hr hr1
      linear_combination -(modeB out) * hn
  · have hh := (h.2.add h.1).mul_left ((Real.sqrt (1 - r) : ℂ) / 2)
    convert hh using 1
    · ext p
      rw [(external_negative_zero_boundary out p hr hr1).2]
      ring
    · ring

/-- The full original J or T generator, before identifying a candidate germ. -/
def kernelMode (square out out' : Bool) (u v z : ℂ) : ℂ :=
  ∑' pq : ℕ × ℕ, (if square then externalT out pq.1 out' pq.2 z
    else externalJ out pq.1 out' pq.2 z) * u ^ pq.1 * v ^ pq.2

/-- The actual two-mode kernel is differentiated in its first external variable by normal sums. -/
theorem kernelMode_derivative (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    HasSum (fun pq : ℕ × ℕ => (pq.1 : ℂ) *
      (if square then externalT out pq.1 out' pq.2 z else externalJ out pq.1 out' pq.2 z) *
        u ^ (pq.1 - 1) * v ^ pq.2)
      (deriv (fun w => kernelMode square out out' w v z) u) := by
  obtain ⟨R, huR, hR⟩ := exists_between (show ‖u‖ < 1 - ‖z‖ by linarith)
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg u) huR
  let K := fun pq : ℕ × ℕ => if square then externalT out pq.1 out' pq.2 z
    else externalJ out pq.1 out' pq.2 z
  have hRz : ‖(R : ℂ)‖ + ‖z‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0] using
      (show R + ‖z‖ < 1 by linarith)
  have hpair := external_kernel_mode_summable out out' hRz hv
  have hs : Summable (fun pq : ℕ × ℕ => ‖K pq * (R : ℂ) ^ pq.1 * v ^ pq.2‖) := by
    cases square
    · simpa only [K, Bool.false_eq_true, ite_false, norm_mul, mul_comm, mul_left_comm,
        mul_assoc] using hpair.1
    · simpa only [K, ite_true, norm_mul, mul_comm, mul_left_comm, mul_assoc] using hpair.2
  have hd (pq : ℕ × ℕ) : DifferentiableOn ℂ
      (fun w : ℂ => K pq * w ^ pq.1 * v ^ pq.2) (Metric.ball 0 R) :=
    fun w _ => (((hasDerivAt_pow pq.1 w).const_mul _).mul_const _)
      |>.differentiableAt.differentiableWithinAt
  have hb (pq : ℕ × ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      ‖K pq * w ^ pq.1 * v ^ pq.2‖ ≤ ‖K pq * (R : ℂ) ^ pq.1 * v ^ pq.2‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    gcongr
    exact (show ‖w‖ < R by simpa using hw).le
  have hu' : u ∈ Metric.ball (0 : ℂ) R := by simpa using huR
  have h := Complex.hasSum_deriv_of_summable_norm hs hd Metric.isOpen_ball hb hu'
  simpa only [deriv_mul_const_field, deriv_const_mul_field, deriv_pow_field,
    kernelMode, K, mul_assoc, mul_left_comm] using h

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
