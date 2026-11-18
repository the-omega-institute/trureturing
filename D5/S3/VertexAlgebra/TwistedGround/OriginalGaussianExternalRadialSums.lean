/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadialSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Radial differentiation of the full literal square-resolvent mode generator. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations

/-! Local complex normal convergence transports the original fixed-mode radial derivative. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
open OriginalGaussianResolvent OriginalGaussianExternalResolvent
open OriginalGaussianDifferentiation OriginalGaussianAllIndexResolvent
open OriginalGaussianBilinearTranspose OriginalGaussianExternalEvolution
open OriginalGaussianExternalNormal OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalEquations OriginalGaussianExternalRadial

def pairing : H →L[ℂ] H →L[ℂ] ℂ :=
  ({ toFun := sourceBilinearFunctional
     map_add' := by
       intro x y
       ext w
       rw [sourceBilinearFunctional_comm (x + y) w, map_add]
       simp only [add_apply]
       rw [sourceBilinearFunctional_comm w x, sourceBilinearFunctional_comm w y]
     map_smul' := by
       intro a x
       ext w
       simp only [RingHom.id_apply, smul_apply, smul_eq_mul]
       exact sourceBilinearFunctional_smul_left a x w } : H →ₗ[ℂ] H →L[ℂ] ℂ).mkContinuous
    1 (by
      intro x
      change ‖sourceBilinearFunctional x‖ ≤ 1 * ‖x‖
      simp only [sourceBilinearFunctional, innerSL_apply_norm, norm_star, one_mul, le_refl])

private lemma square_differentiable {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ squareResolvent z := by
  have h := ((hasDerivAt_resolvent hz).differentiableAt.add
    (opposite_differentiable hz)).const_smul (1 / 2 : ℂ)
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
  exact square_half hw

lemma literal_differentiable (out out' : Bool) (p q : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) : DifferentiableAt ℂ (externalT out p out' q) z := by
  have hX := (hasDerivAt_externalVector out p hz).differentiableAt
  have hY := (hasDerivAt_externalVector out' q hz).differentiableAt
  have hSY := (square_differentiable hz).clm_apply hY
  have h := (pairing.hasFDerivAt_of_bilinear hX.hasFDerivAt hSY.hasFDerivAt).differentiableAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
  exact (external_contractions_explicit out p out' q hw).2.2.2.1.symm

private lemma vector_norm_mono (out : Bool) (p : ℕ) {w : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hR1 : R < 1) (hw : ‖w‖ ≤ R) :
    ‖externalVector out p w‖ ≤ ‖externalVector out p (R : ℂ)‖ := by
  have hw1 : ‖w‖ < 1 := hw.trans_lt hR1
  have hRc : ‖(R : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hR] using hR1
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [externalVector_apply out p hw1, externalVector_apply out p hRc]
  simp only [externalColumn, norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hR]
  gcongr

set_option maxHeartbeats 800000 in
-- The complete complex double mode series is bounded by the two larger-radius vectors.
private lemma kernel_complex_derivative (out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    HasSum (fun pq : ℕ × ℕ => deriv (externalT out pq.1 out' pq.2) z *
      u ^ pq.1 * v ^ pq.2)
      (deriv (fun w => kernelMode true out out' u v w) z) ∧
    DifferentiableAt ℂ (fun w => kernelMode true out out' u v w) z := by
  obtain ⟨R, hzR, hR⟩ := exists_between
    (show ‖z‖ < min (1 - ‖u‖) (1 - ‖v‖) by
      simp only [lt_min_iff]; constructor <;> linarith)
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR
  have hR1 : R < 1 := by have := (lt_min_iff.mp hR).1; linarith [norm_nonneg u]
  have huR : ‖u‖ + ‖(R : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    have := (lt_min_iff.mp hR).1
    linarith
  have hvR : ‖v‖ + ‖(R : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    have := (lt_min_iff.mp hR).2
    linarith
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg u]
  let C := ‖squareResolvent z‖ + 1
  have hS : ∀ᶠ w in 𝓝 z, ‖squareResolvent w‖ < C :=
    (square_differentiable hz).continuousAt.norm.eventually_lt_const (by dsimp [C]; linarith)
  have hball : ∀ᶠ w in 𝓝 z, ‖w‖ < R :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hzR
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp (hball.and hS)
  have hs := (externalVector_mode_summable out huR).mul_of_nonneg
    (externalVector_mode_summable out' hvR) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  let b := fun pq : ℕ × ℕ => C *
    (‖u ^ pq.1 • externalVector out pq.1 (R : ℂ)‖ *
      ‖v ^ pq.2 • externalVector out' pq.2 (R : ℂ)‖)
  have hb : Summable b := hs.mul_left C
  have hd (pq : ℕ × ℕ) : DifferentiableOn ℂ
      (fun w => externalT out pq.1 out' pq.2 w * u ^ pq.1 * v ^ pq.2) U := by
    intro w hw
    exact (((literal_differentiable out out' pq.1 pq.2
      ((hUsub hw).1.trans hR1)).mul_const _).mul_const _).differentiableWithinAt
  have hbound (pq : ℕ × ℕ) (w : ℂ) (hw : w ∈ U) :
      ‖externalT out pq.1 out' pq.2 w * u ^ pq.1 * v ^ pq.2‖ ≤ b pq := by
    have hwR := (hUsub hw).1
    rw [← (external_contractions_explicit out pq.1 out' pq.2 (hwR.trans hR1)).2.2.2.1]
    change ‖inner ℂ (star (externalVector out pq.1 w))
      (squareResolvent w (externalVector out' pq.2 w)) * u ^ pq.1 * v ^ pq.2‖ ≤ _
    simp only [norm_mul, b, norm_smul, norm_pow]
    calc
      _ ≤ (‖externalVector out pq.1 w‖ *
          (‖squareResolvent w‖ * ‖externalVector out' pq.2 w‖)) *
            ‖u‖ ^ pq.1 * ‖v‖ ^ pq.2 := by
        gcongr
        exact (norm_inner_le_norm _ _).trans (by
          rw [norm_star]
          gcongr
          exact (squareResolvent w).le_opNorm _)
      _ ≤ (‖externalVector out pq.1 (R : ℂ)‖ *
          (C * ‖externalVector out' pq.2 (R : ℂ)‖)) * ‖u‖ ^ pq.1 * ‖v‖ ^ pq.2 := by
        gcongr
        · exact vector_norm_mono out pq.1 hR0.le hR1 hwR.le
        · exact (hUsub hw).2.le
        · exact vector_norm_mono out' pq.2 hR0.le hR1 hwR.le
      _ = _ := by ring
  have hderiv := Complex.hasSum_deriv_of_summable_norm hb hd hUopen hbound hzU
  constructor
  · simpa only [deriv_mul_const_field, kernelMode, ite_true] using hderiv
  · exact (Complex.differentiableOn_tsum_of_summable_norm hb hd hUopen hbound).differentiableAt
      (hUopen.mem_nhds hzU)

/-- The real radial derivative of the full literal T generator is the sum of its true derivatives. -/
theorem kernelMode_radial_derivative (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    HasSum (fun pq : ℕ × ℕ =>
      deriv (fun t : ℝ => externalT out pq.1 out' pq.2 (Real.sqrt t : ℂ)) r *
        u ^ pq.1 * v ^ pq.2)
      (deriv (fun t : ℝ => kernelMode true out out' u v (Real.sqrt t : ℂ)) r) := by
  have hu' : ‖u‖ + ‖(Real.sqrt r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hu
  have hv' : ‖v‖ + ‖(Real.sqrt r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hv
  have hz : ‖(Real.sqrt r : ℂ)‖ < 1 := by linarith [norm_nonneg u]
  have h := kernel_complex_derivative out out' hu' hv'
  let a : ℂ := ((1 / (2 * Real.sqrt r) : ℝ) : ℂ)
  have he (f : ℂ → ℂ) (hf : DifferentiableAt ℂ f (Real.sqrt r : ℂ)) :
      deriv (fun t : ℝ => f (Real.sqrt t : ℂ)) r =
        a * deriv f (Real.sqrt r : ℂ) := by
    have hc := hf.hasDerivAt.scomp r (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
    simpa only [smul_eq_mul, a, Function.comp_def] using hc.deriv
  have hh := h.1.mul_left a
  rw [he _ h.2]
  apply hh.congr_fun
  intro pq
  rw [he _ (literal_differentiable out out' pq.1 pq.2 hz)]
  ring


set_option maxHeartbeats 800000 in
-- Absolute normal differentiation is combined with the two genuine signed frequency sums.
/-- ETr holds for the full original T, with the literal source scalars canceled at the zero row. -/
theorem radial_differential (out out' : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    let x : ℂ := r
    let z : ℂ := Real.sqrt r
    let lam := shiftedCentralDerivative x 0 /
      D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
    2 * x * modeScale out u * modeScale out' v *
      deriv (fun t : ℝ => kernelMode true out out' u v (Real.sqrt t : ℂ)) r -
        modeScale out' v * firstModeDerivative true out out' u v z -
        modeScale out u * secondModeDerivative true out out' u v z =
      (1 - x) * OriginalGaussianExternalGenerators.sourceMode out u x *
        OriginalGaussianExternalGenerators.sourceMode out' v x *
          (modeH out u x lam * modeH out' v x lam -
            modeA out u x * modeA out' v x) / 2 := by
  dsimp only
  let x : ℂ := r
  let z : ℂ := Real.sqrt r
  let lam := shiftedCentralDerivative x 0 / D5.S3.Analytic.OriginalHalfBinomialPeriod.period x
  let B := fun e w => ∑' k : ℕ, externalT false 0 e k z * w ^ k
  have hu' : ‖u‖ + ‖z‖ < 1 := by
    simpa only [z, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hu
  have hv' : ‖v‖ + ‖z‖ < 1 := by
    simpa only [z, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hv
  have hF := OriginalGaussianExternalFrequencyRows.external_frequency_generated
    true out out' hu' hv'
  have hF' : HasSum (fun pq : ℕ × ℕ => modeScale out u *
      OriginalGaussianExternalDisplacement.modeFrequency out pq.1
        (fun e k => externalT e k out' pq.2 z) * u ^ pq.1 * v ^ pq.2)
      (firstModeDerivative true out out' u v z - modeB out * B out' v) := by
    cases out <;> simp [firstModeDerivative, modeB, B] at hF ⊢ <;>
      convert hF using 1 <;> ring
  have hS := second_frequency true out out' hu' hv'
  simp only [ite_true] at hS
  have hD := (kernelMode_radial_derivative out out' hr hu hv).mul_left
    (2 * x * modeScale out u * modeScale out' v)
  have hsum := (hD.sub (hF'.mul_left (modeScale out' v))).sub
    (hS.mul_left (modeScale out u))
  have hs := hsum.congr_fun (g := fun pq : ℕ × ℕ =>
    modeScale out u * modeScale out' v *
      (2 * x * deriv (fun t : ℝ => externalT out pq.1 out' pq.2 (Real.sqrt t : ℂ)) r -
        OriginalGaussianExternalDisplacement.modeFrequency out pq.1
          (fun e k => externalT e k out' pq.2 z) -
        OriginalGaussianExternalDisplacement.modeFrequency out' pq.2
          (fun e k => externalT out pq.1 e k z)) * u ^ pq.1 * v ^ pq.2)
    (fun pq => by dsimp [x, z]; ring)
  have hrs : r ≤ Real.sqrt r := Real.le_sqrt_self_iff.mpr hr1.le
  have hur : ‖u‖ + r < 1 := by linarith
  have hvr : ‖v‖ + r < 1 := by linarith
  have he := hs.unique (external_radial_generated out out' hr hr1 hur hvr)
  dsimp only at he
  have hb (e : Bool) (w : ℂ) (hw : ‖w‖ + r < 1) :
      modeScale e w * B e w = (Real.sqrt (1 - r) : ℂ) / 2 *
        (OriginalGaussianExternalGenerators.sourceMode e w x *
          (modeH e w x lam + modeA e w x)) := by
    simpa only [B, x, z, lam, mul_assoc, tsum_mul_left] using
      (external_negative_zero_generated e hr hr1 hw).2.tsum_eq
  let A := OriginalGaussianSourceEvaluation.sourceAmplitude false 0 x
  let t : ℂ := Real.sqrt (1 - r)
  have hn : t * A = 1 := boundary_normalization hr hr1
  have ht : t ^ 2 = 1 - x := by
    dsimp [t, x]
    norm_cast
    exact Real.sq_sqrt (by linarith)
  have hca : (1 - x) * A = t := by
    rw [← ht, pow_two, mul_assoc, hn, mul_one]
  have hbu := hb out u hur
  have hbv := hb out' v hvr
  change modeScale out u * B out u = t / 2 *
    (OriginalGaussianExternalGenerators.sourceMode out u x *
      (modeH out u x lam + modeA out u x)) at hbu
  change modeScale out' v * B out' v = t / 2 *
    (OriginalGaussianExternalGenerators.sourceMode out' v x *
      (modeH out' v x lam + modeA out' v x)) at hbv
  change _ = (1 - x) * OriginalGaussianExternalGenerators.sourceMode out u x *
      OriginalGaussianExternalGenerators.sourceMode out' v x *
      (modeH out u x lam * modeH out' v x lam - modeA out u x * modeA out' v x) / 2
  change 2 * x * modeScale out u * modeScale out' v * _ -
      modeScale out' v * (firstModeDerivative true out out' u v z - modeB out * B out' v) -
      modeScale out u * (secondModeDerivative true out out' u v z - modeB out' * B out u) =
      (1 - x) *
        ((OriginalGaussianExternalGenerators.sourceMode out u x * modeH out u x lam +
            modeB out * A) *
          (OriginalGaussianExternalGenerators.sourceMode out' v x * modeH out' v x lam +
            modeB out' * A) -
        (OriginalGaussianExternalGenerators.sourceMode out u x * modeA out u x -
            modeB out * A) *
          (OriginalGaussianExternalGenerators.sourceMode out' v x * modeA out' v x -
            modeB out' * A)) / 2 at he
  linear_combination he - (modeB out) * hbv - (modeB out') * hbu +
    ((modeB out) * OriginalGaussianExternalGenerators.sourceMode out' v x *
        (modeH out' v x lam + modeA out' v x) / 2 +
      (modeB out') * OriginalGaussianExternalGenerators.sourceMode out u x *
        (modeH out u x lam + modeA out u x) / 2) * hca

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
