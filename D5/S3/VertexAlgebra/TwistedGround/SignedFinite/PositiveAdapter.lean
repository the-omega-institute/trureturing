/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/PositiveAdapter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/PositiveAdapter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite algebra identifies the signed positive T table with the original t. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.FiniteInverse

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite
open OriginalGaussianFiniteCandidateModes (a h h2 L L_h L_h2 P t)

private theorem H_positive (square : Bool) (r : ℂ) :
    H square true true r = fun p q => if square then h2 p q r else h p q r := by
  funext p q
  simp [H, tConstant, tAlpha, tBeta, tDelta, A]

private theorem n_positive (r : ℂ) (b : ℕ → ℕ → ℂ) :
    mulPoly (nPolynomial true true r) b = fun p q => b p q + A r*shift 1 1 b p q := by
  funext p q
  cases p <;> cases q <;> norm_num [mulPoly, nPolynomial, Fin.sum_univ_succ, shift]

private theorem conv_right_add (a b c : ℕ → ℕ → ℂ) :
    conv a (fun p q => b p q+c p q) = fun p q => conv a b p q+conv a c p q := by
  rw [conv_comm, conv_add, conv_comm b, conv_comm c]

private theorem conv_right_scale (z : ℂ) (a b : ℕ → ℕ → ℂ) :
    conv a (fun p q => z*b p q) = fun p q => z*conv a b p q := by
  rw [conv_comm, conv_scale, conv_comm b]

private theorem positive_stencil_h2 (r : ℂ) :
    stencil 1 1 1 (A r) (fun p q => h2 p q r) = fun p q => h p q r := by
  funext p q
  have hh := OriginalGaussianFiniteCandidateModes.h2_inverse_stencil p q r
  cases p <;> cases q <;>
    simpa [OriginalGaussianFiniteCandidateModes.denominatorStencil,
      OriginalGaussianFiniteCandidateModes.shiftX, OriginalGaussianFiniteCandidateModes.shiftY,
      OriginalGaussianFiniteCandidateModes.shift11, stencil, shift, A] using hh

private theorem convolution_L (H : ℕ → ℕ → ℂ → ℂ) (r : ℂ) :
    conv (fun p q => H p q r) (d true true r) = fun p q => L H p q r := by
  rw [conv_comm]
  rfl

private theorem shift_L (F : ℕ → ℕ → ℂ → ℂ) (r : ℂ) :
    shift 1 1 (fun p q => F p q r) = fun p q => OriginalGaussianFiniteCandidateModes.shift11 F p q r := by
  funext p q
  cases p <;> cases q <;> simp [shift, OriginalGaussianFiniteCandidateModes.shift11]

/-- Exact finite normalizations, for every complex r; no analytic premises. -/
theorem tSigned_positive_eq (p q : ℕ) (r : ℂ) :
    tSigned true true p q r = t p q r := by
  let b := d true true r
  have he (F : ℕ → ℕ → ℂ) :
      conv (fun p q => h2 p q r) (mulPoly (ePolynomial true true r) F) =
        conv (fun p q => h p q r) F := by
    rw [conv_comm, mulPoly_ePolynomial, ← stencil_conv, conv_comm F,
      stencil_conv]
    simp only [tConstant, tAlpha, tBeta, tDelta, Bool.and_true, Bool.or_true,
      Bool.not_true, Bool.false_eq_true, Bool.and_false, ite_true, ite_false]
    rw [positive_stencil_h2]
  have hu : tU true true r = fun p q =>
      r/2*mulPoly (ePolynomial true true r) (fun i j => b i j+A r*shift 1 1 b i j) p q+
        r^2*shift 1 1 b p q := by
    funext p q
    simp only [tU, n_positive, b]
  unfold tSigned
  rw [H_positive, hu]
  simp only [ite_true]
  simp_rw [conv_right_add, conv_right_scale, he, conv_shift]
  simp_rw [conv_right_add, conv_right_scale, conv_shift]
  simp only [b, convolution_L, shift_L, t, P, L_h, L_h2, A, d, m, ite_true]
  ring

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
