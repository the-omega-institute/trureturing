/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalJetSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normally convergent diagonal differentiation of the actual source jet generators. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalModeSums

/-! The radial jet is differentiated on the diagonal, with its frequency correction. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
open OriginalGaussianSourceEvaluation OriginalGaussianExternalFrequency
open OriginalGaussianExternalDisplacement OriginalGaussianExternalMoments
open OriginalGaussianExternalGenerators OriginalGaussianExternalModeSums
open OriginalGaussianExternalSourceJet OriginalGaussianExternalNormal

private def amplitudeCoefficient (out : Bool) (p n : ℕ) : ℂ :=
  (OriginalGaussianMatrix.centralWeight n : ℂ) * (-1 : ℂ) ^ n *
    Ring.choose ((if out then (p : ℂ) + 1 / 2 else -(p : ℂ) - 1 / 2) - 1 / 2) n

private lemma amplitude_normal (out : Bool) (p : ℕ) {R : ℝ} (hR0 : 0 < R)
    (hR : R < 1) :
    DifferentiableOn ℂ (sourceAmplitude out p) (Metric.ball 0 R) ∧
    ∀ w ∈ Metric.ball (0 : ℂ) R,
      ‖sourceAmplitude out p w‖ ≤ ∑' n : ℕ, ‖amplitudeCoefficient out p n * (R : ℂ) ^ n‖ := by
  -- A nonzero mode radius retains every p row of the joint majorant.
  let δ : ℝ := (1 - R) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hj := sourceAmplitude_joint_summable out (u := (δ : ℂ)) (x := (R : ℂ))
    (by simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, abs_of_pos hδ]
        dsimp [δ]; linarith)
  have hs : Summable (fun n : ℕ => ‖amplitudeCoefficient out p n * (R : ℂ) ^ n‖) := by
    have hh := hj.prod_factor p
    simp only [norm_mul, norm_pow, amplitudeCoefficient] at hh ⊢
    have hδ0 : ‖(δ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (by exact_mod_cast hδ.ne')
    exact (summable_mul_right_iff (pow_ne_zero p hδ0)).mp hh
  have hd (n : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ => amplitudeCoefficient out p n * w ^ n) (Metric.ball 0 R) :=
    fun w _ => ((hasDerivAt_pow n w).const_mul _).differentiableAt.differentiableWithinAt
  have hb (n : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      ‖amplitudeCoefficient out p n * w ^ n‖ ≤
        ‖amplitudeCoefficient out p n * (R : ℂ) ^ n‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    gcongr
    exact (show ‖w‖ < R by simpa using hw).le
  constructor
  · exact Complex.differentiableOn_tsum_of_summable_norm hs hd Metric.isOpen_ball hb
  · intro w hw
    have hh : Summable (fun n : ℕ => ‖amplitudeCoefficient out p n * w ^ n‖) :=
      hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hb n w hw)
    exact (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum (fun n => hb n w hw) hs)

lemma amplitude_derivative_mode (out : Bool) {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => deriv (sourceAmplitude out p) x * u ^ p)
      (deriv (fun w => sourceMode out u w) x) ∧
    DifferentiableAt ℂ (fun w => sourceMode out u w) x ∧
    ∀ p, DifferentiableAt ℂ (sourceAmplitude out p) x := by
  obtain ⟨R, hxR, hR⟩ := exists_between (show ‖x‖ < 1 - ‖u‖ by linarith)
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg x) hxR
  have hR1 : R < 1 := by linarith [norm_nonneg u]
  have hs := sourceAmplitude_joint_summable out (u := u) (x := (R : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0] using
      (show ‖u‖ + R < 1 by linarith))
  have hsrow := hs.prod
  have hd (p : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ => sourceAmplitude out p w * u ^ p) (Metric.ball 0 R) :=
    (amplitude_normal out p hR0 hR1).1.mul_const _
  have hb (p : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      ‖sourceAmplitude out p w * u ^ p‖ ≤
        ∑' n : ℕ, ‖amplitudeTerm out u (R : ℂ) (p,n)‖ := by
    simp only [norm_mul]
    calc
      _ ≤ (∑' n : ℕ, ‖amplitudeCoefficient out p n * (R : ℂ) ^ n‖) * ‖u ^ p‖ :=
        mul_le_mul_of_nonneg_right ((amplitude_normal out p hR0 hR1).2 w hw) (norm_nonneg _)
      _ = _ := by
        rw [← tsum_mul_right]
        exact tsum_congr (fun n => by
          simp [amplitudeTerm, amplitudeCoefficient, mul_assoc])
  have hx : x ∈ Metric.ball (0 : ℂ) R := by simpa using hxR
  have hA (p : ℕ) := (amplitude_normal out p hR0 hR1).1.differentiableAt
    (Metric.isOpen_ball.mem_nhds hx)
  have h := Complex.hasSum_deriv_of_summable_norm hsrow hd Metric.isOpen_ball hb hx
  refine ⟨?_, ?_, hA⟩
  · simpa only [deriv_mul_const_field', sourceMode] using h
  · exact (Complex.differentiableOn_tsum_of_summable_norm hsrow hd Metric.isOpen_ball hb)
      |>.differentiableAt (Metric.isOpen_ball.mem_nhds hx)

/-- Diagonal differentiation of the actual A series gives both original jet mode sums. -/
theorem sourceJetMoment_generators {u : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hsmall : ‖u‖ + r < 1) :
    let x : ℂ := r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    HasSum (fun p : ℕ => sourceJetMoment true p x * u ^ p)
      (2 * x * deriv (fun w => sourceMode true u w) x -
        sourceMode true u x * (1 - 2 * u + (1 - x) * u ^ 2) /
          (2 * (1 - (1 - x) * u)) + sourceAmplitude false 0 x / 2 -
        2 * x * sourceMode true u x * lambdaRatio) ∧
    HasSum (fun p : ℕ => u * sourceJetMoment false p x * u ^ p)
      (2 * x * u * deriv (fun w => sourceMode false u w) x -
        sourceMode false u x * (u * (1 - u) / (2 * (1 - x - u)) - 1 / 2) -
        sourceAmplitude false 0 x / 2 - 2 * x * u * sourceMode false u x * lambdaRatio) := by
  dsimp only
  let x : ℂ := r
  let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
    D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
  have hs : ‖u‖ + ‖x‖ < 1 := by
    simpa only [x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hsmall
  have hxr : ‖x‖ < 1 := by linarith [norm_nonneg u]
  have hd (e : Bool) := amplitude_derivative_mode e hs
  have he (e : Bool) (p : ℕ) :
      sourceJetMoment e p x = 2 * x * deriv (sourceAmplitude e p) x -
        sourceMoment e p x - 2 * x * sourceAmplitude e p x * lambdaRatio := by
    have hh := sourceJetMoment_eq_derivative e p hr hr1
    rw [((hd e).2.2 p).hasDerivAt.comp_ofReal.deriv,
      ← sourceMoment_eq_modeFrequency e p hxr] at hh
    dsimp only [lambdaRatio]
    convert hh using 1 <;> ring
  have hA (e : Bool) : HasSum (fun p : ℕ => sourceAmplitude e p x * u ^ p)
      (sourceMode e u x) := (sourceAmplitude_mode_hasSum e hs).summable.hasSum
  have hU := sourceMoment_generators_explicit hs
  constructor
  · have hh := (((hd true).1.mul_left (2 * x)).sub hU.1).sub
      ((hA true).mul_left (2 * x * lambdaRatio))
    convert hh using 1
    · ext p
      rw [he true p]
      ring
    · ring
  · have hh := ((((hd false).1.mul_left (2 * x * u)).sub hU.2).sub
      ((hA false).mul_left (2 * x * u * lambdaRatio)))
    convert hh using 1
    · ext p
      rw [he false p]
      ring
    · ring

lemma diagonal_derivative_explicit (out : Bool) {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1) :
    let b : ℂ := if out then u else -1
    deriv (fun w => sourceMode out u w) x =
      -b * sourceMode out u x / (2 * (1 - u + b * x)) := by
  dsimp only
  let b : ℂ := if out then u else -1
  change deriv (fun w => sourceMode out u w) x =
    -b * sourceMode out u x / (2 * (1 - u + b * x))
  have hne {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
    intro he
    have hh := congrArg norm (sub_eq_zero.mp he)
    simp only [norm_one] at hh
    linarith
  have h1 : 1 - u ≠ 0 := hne (by linarith [norm_nonneg x])
  have hden {w : ℂ} (hw : ‖u‖ + ‖w‖ < 1) : 1 - u + b * w ≠ 0 := by
    cases out
    · have hh : ‖u + w‖ < 1 := lt_of_le_of_lt (norm_add_le _ _) hw
      convert hne hh using 1
      simp only [b, Bool.false_eq_true, ite_false]
      ring
    · have hu : ‖u‖ < 1 := by linarith [norm_nonneg w]
      have hh : ‖(1 - w) * u‖ < 1 := calc
        _ ≤ (1 + ‖w‖) * ‖u‖ := by
          rw [norm_mul]
          gcongr
          simpa only [norm_one] using norm_sub_le (1 : ℂ) w
        _ ≤ ‖u‖ + ‖w‖ := by nlinarith [norm_nonneg w]
        _ < 1 := hw
      convert hne hh using 1
      simp only [b, ite_true]
      ring
  have hsquare {w : ℂ} (hw : ‖u‖ + ‖w‖ < 1) :
      sourceMode out u w ^ 2 * ((1 - u) * (1 - u + b * w)) = 1 := by
    have he : sourceMode out u w ^ 2 = 1 / ((1 - u) * (1 - u + b * w)) := by
      have hh := sourceMode_square hw
      cases out
      · have he : 1 - u + b * w = 1 - w - u := by simp only [b, Bool.false_eq_true, ite_false]; ring
        rw [he]
        exact hh.2
      · have he : 1 - u + b * w = 1 - (1 - w) * u := by simp only [b, ite_true]; ring
        rw [he]
        exact hh.1
    rw [he]
    exact div_mul_cancel₀ _ (mul_ne_zero h1 (hden hw))
  have hm := (amplitude_derivative_mode out hsmall).2.1.hasDerivAt
  have hd := ((hasDerivAt_const x (1 - u : ℂ)).add
    ((hasDerivAt_id x).const_mul b)).const_mul (1 - u)
  have he : (fun w => sourceMode out u w ^ 2 * ((1 - u) * (1 - u + b * w)))
      =ᶠ[𝓝 x] (fun _ => 1) := by
    have hn : ∀ᶠ w : ℂ in 𝓝 x, ‖u‖ + ‖w‖ < 1 :=
      (continuousAt_const.add continuous_norm.continuousAt).eventually (gt_mem_nhds hsmall)
    exact hn.mono (fun _ hw => hsquare hw)
  have hz := (((hm.pow 2).mul hd).congr_of_eventuallyEq he.symm).unique
    (hasDerivAt_const x (1 : ℂ))
  dsimp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, id_eq] at hz
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_add, mul_one] at hz
  have hM : sourceMode out u x ≠ 0 := by
    intro hzero
    have hh := hsquare hsmall
    norm_num [hzero] at hh
  have hlin : 2 * (1 - u + b * x) * deriv (fun w => sourceMode out u w) x +
      b * sourceMode out u x = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hM h1)
    linear_combination hz
  have h2 := hden hsmall
  have h2' : 1 - u + x * b ≠ 0 := by simpa only [mul_comm] using h2
  field_simp [h2, h2']
  linear_combination hlin

/-- The jet amplitudes are explicit rational expressions of the actual mode generators. -/
theorem sourceJetMoment_generators_explicit {u : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hsmall : ‖u‖ + r < 1) :
    let x : ℂ := r
    let lambdaRatio := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    HasSum (fun p : ℕ => sourceJetMoment true p x * u ^ p)
      (sourceMode true u x *
        (-x * u / (1 - (1 - x) * u) -
          (1 - 2 * u + (1 - x) * u ^ 2) / (2 * (1 - (1 - x) * u)) - 2 * x * lambdaRatio) +
        sourceAmplitude false 0 x / 2) ∧
    HasSum (fun p : ℕ => u * sourceJetMoment false p x * u ^ p)
      (sourceMode false u x *
        (x * u / (1 - x - u) -
          (u * (1 - u) / (2 * (1 - x - u)) - 1 / 2) - 2 * x * u * lambdaRatio) -
        sourceAmplitude false 0 x / 2) := by
  have hs : ‖u‖ + ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hsmall
  have h := sourceJetMoment_generators hr hr1 hsmall
  dsimp only at h ⊢
  rw [diagonal_derivative_explicit true hs, diagonal_derivative_explicit false hs] at h
  simp only [ite_true, Bool.false_eq_true, ite_false, neg_neg, one_mul] at h
  have he : 1 - u + u * (r : ℂ) = 1 - (1 - (r : ℂ)) * u := by ring
  have hn : 1 - u + -1 * (r : ℂ) = 1 - (r : ℂ) - u := by ring
  rw [he, hn] at h
  constructor
  · convert h.1 using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · convert h.2 using 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalJetSums
