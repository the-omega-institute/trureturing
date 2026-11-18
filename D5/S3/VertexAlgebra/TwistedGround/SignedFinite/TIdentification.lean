/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/TIdentification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/TIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All signed natural Gaussian T modes equal explicit finite tables. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.JIdentification
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.FiniteInverse

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite
open OriginalGaussianExternalResolvent OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalGenerators
open OriginalGaussianFiniteCandidateModes (k)
open OriginalGaussianExternalSignedCandidate (E N candidateT rationalT E_ne_zero)

private theorem actualT_stencil (e f : Bool) {z : ℂ} (hz : ‖z‖<1) :
    mulPoly (ePolynomial e f (z^2)) (mulPoly (ePolynomial e f (z^2))
      (fun p q => externalT e p f q z + k (z^2)*d e f (z^2) p q)) = tU e f (z^2) := by
  let r := z^2
  have hr : ‖r‖<1 := by dsimp [r]; rw [norm_pow]; nlinarith [norm_nonneg z]
  have hd := source_jointSeries e f hr
  have hl := (((kernel_jointSeries true e f hz).add (hd.scale (k r))).polynomial_mul
    (ePolynomial e f r)).polynomial_mul (ePolynomial e f r)
  have hn := ((((hd.polynomial_mul (nPolynomial e f r)).polynomial_mul (ePolynomial e f r)).scale
    (r/2)).add ((hd.mul_monomial 1 1).scale (r^2)))
  let F := fun u v => (r/2)*(E e f u v r*(N e f u v r*
    (sourceMode e u r*sourceMode f v r))) + r^2*(u*v*(sourceMode e u r*sourceMode f v r))
  have hn' : JointSeries F (tU e f r) := by
    change JointSeries F (fun p q => r/2*mulPoly (ePolynomial e f r)
      (mulPoly (nPolynomial e f r) (fun i j => m e i r*m f j r)) p q+
      r^2*shift 1 1 (fun i j => m e i r*m f j r) p q)
    simpa only [F, eval_ePolynomial, eval_nPolynomial, pow_one] using hn
  have hl' : JointSeries F (mulPoly (ePolynomial e f r) (mulPoly (ePolynomial e f r)
      (fun p q => externalT e p f q z+k r*d e f r p q))) := by
    apply hl.congr_disk (S := min (1-‖z‖) (1-‖r‖)) (lt_min (by linarith) (by linarith))
    intro u v hu hv
    have huz : ‖u‖+‖z‖<1 := by have := hu.trans_le (min_le_left _ _); linarith
    have hvz : ‖v‖+‖z‖<1 := by have := hv.trans_le (min_le_left _ _); linarith
    have hE : E e f u v r ≠ 0 := E_ne_zero e f
      (by simpa only [r, norm_pow, Real.sqrt_sq (norm_nonneg z)] using huz)
      (by simpa only [r, norm_pow, Real.sqrt_sq (norm_nonneg z)] using hvz)
    simp only [eval_ePolynomial]
    rw [(OriginalGaussianComplexRadialContinuation.allSignsJT_eq_candidates_complex e f huz hvz).2]
    unfold F OriginalGaussianExternalSignedCandidate.candidateT rationalT
    change E e f u v r*(E e f u v r*(_+_)) = _
    have hk : k r = OriginalGaussianExternalAnalyticCandidate.correction r := rfl
    rw [hk]
    dsimp only [r] at hE ⊢
    field_simp [hE]
    <;> ring
  exact hl'.unique hn' (fun _ _ => rfl)

/-- All four sectors, all natural indices and all complex points of the unit disk. -/
theorem externalT_signed_finite_eq (e f : Bool) (p q : ℕ) {z : ℂ} (hz : ‖z‖<1) :
    externalT e p f q z = tSigned e f p q (z^2) := by
  have hr : ‖z^2‖<1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have he := congrFun (congrFun (squared_stencil_inverse e f hr _ _ (actualT_stencil e f hz)) p) q
  unfold tSigned
  linear_combination he

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
