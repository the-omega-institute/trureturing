/- GID: D5/S3/VertexAlgebra/TwistedGround/Signed/Identification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Signed/Identification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Gaussian J and T identification in six signed sectors. -/

import D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial
import D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSignedIdentification
open OriginalGaussianExternalGenerators OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalEquations
open OriginalGaussianExternalSignedCandidate
open OriginalGaussianExternalAnalyticCandidate (b)

private def signedCandidate (square e f : Bool) (u v r : ℂ) : ℂ :=
  if square then candidateT e f u v r else candidateJ e f u v r

private def sigma (square : Bool) : ℂ := if square then -1 else 1

private def spatial (square e f : Bool) (F : ℂ × ℂ → ℂ) (u v : ℂ) : ℂ :=
  modeScale f v * L e (fun w => F (w, v)) u +
    sigma square * modeScale e u * L f (fun w => F (u, w)) v

-- These are literal definitional matches, with the original beta and b=1-u.
private lemma L_kernel_first (square e f : Bool) (u v z : ℂ) :
    L e (fun w => kernelMode square e f w v z) u =
      firstModeDerivative square e f u v z := rfl

private lemma L_kernel_second (square e f : Bool) (u v z : ℂ) :
    L f (fun w => kernelMode square e f u w z) v =
      secondModeDerivative square e f u v z := rfl

-- The uniqueness supplier writes 1+u where the original operator writes u+1.
private lemma beta_eq (e : Bool) (u : ℂ) :
    beta e u = (if e then (1 - 3 * u) / 2 else -(1 + u) / 2) := by
  cases e <;> simp only [beta, Bool.false_eq_true, ite_false, ite_true] <;> ring

-- Slice differentiability is obtained from JOINT Frechet differentiability.
-- In particular deriv_sub is never applied merely to a formal mode sum.
private lemma spatial_sub (square e f : Bool) {F G : ℂ × ℂ → ℂ} {u v : ℂ}
    (hF : DifferentiableAt ℂ F (u, v)) (hG : DifferentiableAt ℂ G (u, v)) :
    spatial square e f (F - G) u v =
      spatial square e f F u v - spatial square e f G u v := by
  have hFu : DifferentiableAt ℂ (fun w => F (w, v)) u :=
    (hF.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))).differentiableAt
  have hFv : DifferentiableAt ℂ (fun w => F (u, w)) v :=
    (hF.hasFDerivAt.comp_hasDerivAt v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))).differentiableAt
  have hGu : DifferentiableAt ℂ (fun w => G (w, v)) u :=
    (hG.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))).differentiableAt
  have hGv : DifferentiableAt ℂ (fun w => G (u, w)) v :=
    (hG.hasFDerivAt.comp_hasDerivAt v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))).differentiableAt
  have hdu : deriv (fun w => (F - G) (w, v)) u =
      deriv (fun w => F (w, v)) u - deriv (fun w => G (w, v)) u :=
    deriv_sub hFu hGu
  have hdv : deriv (fun w => (F - G) (u, w)) v =
      deriv (fun w => F (u, w)) v - deriv (fun w => G (u, w)) v :=
    deriv_sub hFv hGv
  unfold spatial L
  rw [hdu, hdv]
  simp only [Pi.sub_apply]
  ring

-- Both equations below have the SAME actual A/H source, period ratio, and,
-- for J, the SAME modeB e * modeB f. The J constant is retained in hK and hC
-- until equality is obtained by transitivity; it is never dropped beforehand.
private lemma original_candidate_spatial_eq (square e f : Bool)
    {u v : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    spatial square e f
        (fun p : ℂ × ℂ => kernelMode square e f p.1 p.2 (Real.sqrt r : ℂ)) u v =
      spatial square e f
        (fun p : ℂ × ℂ => signedCandidate square e f p.1 p.2 (r : ℂ)) u v := by
  cases square
  · have hK := (displacement_differential e f hr hr1 hu hv).1
    have hC := candidateJ_original_displacement e f hr hr1 hu hv
    dsimp only at hK hC
    simpa only [spatial, signedCandidate, sigma, Bool.false_eq_true, ite_false,
      one_mul, L_kernel_first, L_kernel_second] using hK.trans hC.symm
  · have hK := (displacement_differential e f hr hr1 hu hv).2
    have hC := candidateT_original_displacement e f hr hr1 hu hv
    dsimp only at hK hC
    simpa only [spatial, signedCandidate, sigma, ite_true, neg_one_mul, one_mul,
      neg_mul, sub_eq_add_neg, L_kernel_first, L_kernel_second] using hK.trans hC.symm

private theorem six_sector_identification (square e f : Bool)
    {u v : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1)
    (hneg : e = false ∨ f = false) :
    kernelMode square e f u v (Real.sqrt r : ℂ) =
      signedCandidate square e f u v (r : ℂ) := by
  let Rreal : ℝ := 1 - Real.sqrt r
  let K : ℂ × ℂ → ℂ :=
    fun p => kernelMode square e f p.1 p.2 (Real.sqrt r : ℂ)
  let C : ℂ × ℂ → ℂ := fun p => signedCandidate square e f p.1 p.2 (r : ℂ)
  let F : ℂ × ℂ → ℂ := K - C
  have hsnonneg : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
  have hslt : Real.sqrt r < 1 := by nlinarith
  have hRpos : 0 < Rreal := by dsimp [Rreal]; linarith
  have hRone : Rreal ≤ 1 := by dsimp [Rreal]; linarith
  have hnorm : ‖(Real.sqrt r : ℂ)‖ = Real.sqrt r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsnonneg]
  have hdomain (a : ℂ) (ha : ‖a‖ < Rreal) : ‖a‖ + Real.sqrt r < 1 := by
    dsimp [Rreal] at ha
    linarith
  have hk (a b : ℂ) (ha : ‖a‖ < Rreal) (hb : ‖b‖ < Rreal) :
      DifferentiableAt ℂ K (a, b) := by
    apply OriginalGaussianExternalAnalyticCandidate.kernelMode_joint_differentiable
      square e f
    · simpa only [hnorm] using hdomain a ha
    · simpa only [hnorm] using hdomain b hb
  have hc (a b : ℂ) (ha : ‖a‖ < Rreal) (hb : ‖b‖ < Rreal) :
      DifferentiableAt ℂ C (a, b) := by
    have h := candidates_original_joint_differentiable e f hr hr1
      (hdomain a ha) (hdomain b hb)
    cases square
    · simpa only [C, signedCandidate, Bool.false_eq_true, ite_false] using h.1
    · simpa only [C, signedCandidate, ite_true] using h.2
  have hdiff (a b : ℂ) (ha : ‖a‖ < Rreal) (hb : ‖b‖ < Rreal) :
      DifferentiableAt ℂ F (a, b) :=
    (hk a b ha hb).sub (hc a b ha hb)
  have hpde (a b : ℂ) (ha : ‖a‖ < Rreal) (hb : ‖b‖ < Rreal) :
      spatial square e f F a b = 0 := by
    change spatial square e f (K - C) a b = 0
    rw [spatial_sub square e f (hk a b ha hb) (hc a b ha hb)]
    exact sub_eq_zero.mpr (original_candidate_spatial_eq square e f hr hr1
      (hdomain a ha) (hdomain b hb))
  have hzero : ∀ a b : ℂ, ‖a‖ < Rreal → ‖b‖ < Rreal → F (a, b) = 0 := by
    apply Signed.SpatialUniqueness.signed_spatial_zero
      hRpos hRone F e f square hneg hdiff
    intro a b ha hb
    simpa only [spatial, L, OriginalGaussianExternalAnalyticCandidate.b,
      beta_eq, modeScale, sigma] using hpde a b ha hb
  have huR : ‖u‖ < Rreal := by dsimp [Rreal]; linarith
  have hvR : ‖v‖ < Rreal := by dsimp [Rreal]; linarith
  have hend : kernelMode square e f u v (Real.sqrt r : ℂ) -
      signedCandidate square e f u v (r : ℂ) = 0 := by
    simpa only [F, K, C, Pi.sub_apply] using hzero u v huR hvR
  exact sub_eq_zero.mp hend

/-- actual original J identification in all three negative-label
sectors, on the entire original bidisk including axes, origin and diagonal. -/
theorem signedJ_eq_candidateJ (e f : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1)
    (hneg : e = false ∨ f = false) :
    kernelMode false e f u v (Real.sqrt r : ℂ) =
      OriginalGaussianExternalSignedCandidate.candidateJ e f u v (r : ℂ) := by
  simpa only [signedCandidate, Bool.false_eq_true, ite_false] using
    six_sector_identification false e f hr hr1 hu hv hneg

/-- actual original T identification in all three negative-label
sectors, on the entire original bidisk including axes, origin and diagonal. -/
theorem signedT_eq_candidateT (e f : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1)
    (hneg : e = false ∨ f = false) :
    kernelMode true e f u v (Real.sqrt r : ℂ) =
      OriginalGaussianExternalSignedCandidate.candidateT e f u v (r : ℂ) := by
  simpa only [signedCandidate, ite_true] using
    six_sector_identification true e f hr hr1 hu hv hneg

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSignedIdentification
