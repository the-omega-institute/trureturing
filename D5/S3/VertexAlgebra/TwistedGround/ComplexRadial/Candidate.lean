/- GID: D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphy of the literal signed candidates on the original complex source disk. -/


import D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The literal signed candidates are holomorphic after composition with the radial square. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianComplexRadialContinuation
open OriginalGaussianExternalGenerators OriginalGaussianExternalModeSums
open OriginalGaussianExternalJetSums OriginalGaussianExternalSignedCandidate
open OriginalGaussianExternalAnalyticCandidate (b correction)
open D5.S3.Analytic.OriginalHalfBinomialPeriod (period)

/-- The exact common radius of the two original source inequalities. -/
def sourceRadius (u v : ℂ) : ℝ := min (1 - ‖u‖) (1 - ‖v‖)

lemma norm_lt_sourceRadius_iff (u v z : ℂ) :
    ‖z‖ < sourceRadius u v ↔ ‖u‖ + ‖z‖ < 1 ∧ ‖v‖ + ‖z‖ < 1 := by
  unfold sourceRadius
  rw [lt_min_iff]
  constructor
  · rintro ⟨hu, hv⟩
    constructor <;> linarith
  · rintro ⟨hu, hv⟩
    constructor <;> linarith

lemma sourceRadius_pos {u v : ℂ} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    0 < sourceRadius u v := by
  exact lt_min (sub_pos.mpr hu) (sub_pos.mpr hv)

lemma sourceRadius_le_one (u v : ℂ) : sourceRadius u v ≤ 1 := by
  have h := min_le_left (1 - ‖u‖) (1 - ‖v‖)
  dsimp only [sourceRadius]
  linarith [norm_nonneg u]

private lemma sqrt_norm_square (z : ℂ) : Real.sqrt ‖z ^ 2‖ = ‖z‖ := by
  rw [norm_pow, Real.sqrt_sq (norm_nonneg z)]

private lemma source_square_small {u z : ℂ} (hu : ‖u‖ + ‖z‖ < 1) :
    ‖u‖ + ‖z ^ 2‖ < 1 := by
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg u]
  have hs : ‖z‖ ^ 2 ≤ ‖z‖ := by
    nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hz.le)]
  rw [norm_pow]
  linarith

private lemma W_source_square_sum_ne_zero (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    W e u (z ^ 2) + W f v (z ^ 2) ≠ 0 := by
  exact W_sum_ne_zero e f (source_square_small hu) (source_square_small hv)

/-- The signed E bound uses the original source radius through the exact sqrt norm. -/
private lemma E_source_square_ne_zero (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    E e f u v (z ^ 2) ≠ 0 := by
  exact E_ne_zero e f (by rwa [sqrt_norm_square]) (by rwa [sqrt_norm_square])

-- This varies the AMPLITUDE r, not the source coordinate u.
private lemma source_amplitude_differentiable (e : Bool) {u r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) :
    DifferentiableAt ℂ (fun w => sourceMode e u w) r := by
  exact (amplitude_derivative_mode e hu).2.1

private lemma source_square_differentiable (e : Bool) {u z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w => sourceMode e u (w ^ 2)) z := by
  have hsrc : DifferentiableAt ℂ (fun w => sourceMode e u w) (z ^ 2) :=
    source_amplitude_differentiable e (source_square_small hu)
  have hsq : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := differentiableAt_id.pow 2
  exact hsrc.comp z hsq

private lemma W_square_differentiable (e : Bool) {u z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w => W e u (w ^ 2)) z := by
  have hh : DifferentiableAt ℂ (fun w => h e u (w ^ 2)) z := by
    cases e <;> simp only [h, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  exact hh.mul (source_square_differentiable e hu)

private lemma correction_square_differentiable {u z : ℂ} (hu : ‖u‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w => correction (w ^ 2)) z := by
  have hr : ‖z ^ 2‖ < 1 := by
    have h := source_square_small hu
    linarith [norm_nonneg u]
  have hc : DifferentiableAt ℂ correction (z ^ 2) :=
    (OriginalGaussianExternalAnalyticCandidate.correction_hasDerivAt hr).differentiableAt
  have hsq : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := differentiableAt_id.pow 2
  exact hc.comp z hsq

private lemma candidateT_square_differentiable (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w => candidateT e f u v (w ^ 2)) z := by
  have hMu := source_square_differentiable e hu
  have hMv := source_square_differentiable f hv
  have hc := correction_square_differentiable hu
  have he := E_source_square_ne_zero e f hu hv
  have hE : DifferentiableAt ℂ (fun w => E e f u v (w ^ 2)) z := by
    unfold E
    fun_prop
  have hN : DifferentiableAt ℂ (fun w => N e f u v (w ^ 2)) z := by
    cases e <;> cases f <;> simp only [N, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hsq : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := differentiableAt_id.pow 2
  have ht₁ := (hsq.mul hN).div (hE.const_mul 2) (mul_ne_zero (by norm_num) he)
  have ht₂ := (((hsq.pow 2).mul_const u).mul_const v).div
    (hE.pow 2) (pow_ne_zero 2 he)
  exact (hMu.mul hMv).mul ((ht₁.add ht₂).sub hc)

private lemma candidateJ_square_differentiable (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w => candidateJ e f u v (w ^ 2)) z := by
  have hMu := source_square_differentiable e hu
  have hMv := source_square_differentiable f hv
  have hc := correction_square_differentiable hu
  have hWu := W_square_differentiable e hu
  have hWv := W_square_differentiable f hv
  have hs := W_source_square_sum_ne_zero e f hu hv
  have hbu : b u ≠ 0 := (mode_factors_ne_zero (source_square_small hu)).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero (source_square_small hv)).1
  have hden := ((hWu.add hWv).pow 2).const_mul (4 * b u * b v)
  have hd : 4 * b u * b v * (W e u (z ^ 2) + W f v (z ^ 2)) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hbu) hbv) (pow_ne_zero 2 hs)
  have hsq : DifferentiableAt ℂ (fun w : ℂ => w ^ 2) z := differentiableAt_id.pow 2
  have hnum := (hsq.pow 2).mul_const (rho e f u v)
  exact (hMu.mul hMv).mul (((hsq.div_const 4).sub hc).add (hnum.div hden hd))

/-- The literal signed formula selected by the SAME Bool as kernelMode. -/
def signedCandidate (square e f : Bool) (u v r : ℂ) : ℂ :=
  if square then candidateT e f u v r else candidateJ e f u v r

private lemma candidate_square_differentiable (square e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun w => signedCandidate square e f u v (w ^ 2)) z := by
  cases square
  · exact candidateJ_square_differentiable e f hu hv
  · exact candidateT_square_differentiable e f hu hv

/-- No pole-free larger r-domain is asserted for T. The disk here is in z. -/
lemma candidate_square_analyticOnNhd (square e f : Bool) (u v : ℂ) :
    AnalyticOnNhd ℂ (fun z => signedCandidate square e f u v (z ^ 2))
      (Metric.ball 0 (sourceRadius u v)) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro z hz
  have hzR : ‖z‖ < sourceRadius u v := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hd := (norm_lt_sourceRadius_iff u v z).1 hzR
  exact (candidate_square_differentiable square e f hd.1 hd.2).differentiableWithinAt

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianComplexRadialContinuation
