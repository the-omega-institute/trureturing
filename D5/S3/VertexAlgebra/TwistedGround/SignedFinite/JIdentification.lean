/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/JIdentification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/JIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All signed natural Gaussian J modes equal explicit finite tables. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Tables
import D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Applications

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite
open OriginalGaussianExternalResolvent OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalGenerators
open OriginalGaussianFiniteCandidateModes (k)
open OriginalGaussianExternalSignedCandidate (G Qconstant jN rho)

/-- The actual original kernels supply the local coefficient sums. -/
theorem kernel_jointSeries (square e f : Bool) {z : ℂ} (hz : ‖z‖ < 1) :
    JointSeries (fun u v => kernelMode square e f u v z)
      (fun p q => if square then externalT e p f q z else externalJ e p f q z) := by
  refine ⟨1-‖z‖, by linarith, fun u v hu hv => ?_⟩
  have hs := OriginalGaussianExternalNormal.external_kernel_mode_summable e f
    (by linarith : ‖u‖+‖z‖<1) (by linarith : ‖v‖+‖z‖<1)
  have hh : Summable (fun pq : ℕ × ℕ =>
      (if square then externalT e pq.1 f pq.2 z else externalJ e pq.1 f pq.2 z) *
        u^pq.1*v^pq.2) := by
    cases square
    · exact (hs.1.congr (fun pq => by simp only [Bool.false_eq_true, ite_false, ite_true]; congr 1; ring)).of_norm
    · exact (hs.2.congr (fun pq => by simp only [Bool.false_eq_true, ite_false, ite_true]; congr 1; ring)).of_norm
  exact hh.hasSum

theorem jointSeries_jStencil {F a} (h : JointSeries F a) (e f : Bool) :
    JointSeries (fun u v => 2*G e f u v^2*F u v) (jStencil (e == f) a) := by
  by_cases hef : e = f
  · have hh := (((h.mul_monomial 2 0).sub ((h.mul_monomial 1 1).scale 2)).add (h.mul_monomial 0 2)).scale 2
    convert hh using 1
    · funext u v; simp [G, hef] <;> ring
    · funext p q; simp [jStencil, hef]
  · have hh := ((h.sub ((h.mul_monomial 1 1).scale 2)).add (h.mul_monomial 2 2)).scale 2
    convert hh using 1
    · funext u v; simp [G, hef] <;> ring
    · funext p q; simp [jStencil, hef]

theorem jointSeries_rho (e f : Bool) :
    JointSeries (rho e f) (rhoTable (e == f)) := by
  by_cases hef : e = f
  · have hh := (jointSeries_atom 1 0 1).add (jointSeries_atom 0 1 1)
    convert hh using 1
    · funext u v; simp [rho, hef]
    · simp [rhoTable, hef]
  · have hh := ((jointSeries_atom 0 0 1).add (jointSeries_atom 1 1 1)).scale (-1)
    convert hh using 1
    · funext u v; simp [rho, hef] <;> ring
    · funext p q; simp [rhoTable, hef] <;> ring

private theorem square_small {z : ℂ} (hz : ‖z‖ < 1) : ‖z^2‖ < 1 := by
  rw [norm_pow]
  nlinarith [norm_nonneg z]

private theorem actualJ_stencil (e f : Bool) {z : ℂ} (hz : ‖z‖ < 1) :
    jStencil (e == f) (fun p q => externalJ e p f q z -
      (Qconstant e f (z^2)-k (z^2))*d e f (z^2) p q) = jS e f (z^2) := by
  let r := z^2
  have hr : ‖r‖<1 := square_small hz
  have hd := source_jointSeries e f hr
  have hl := jointSeries_jStencil ((kernel_jointSeries false e f hz).sub
    (hd.scale (Qconstant e f r-k r))) e f
  have hn := (hd.polynomial_mul (jNumerator e f r)).sub (jointSeries_rho e f)
  have hn' : JointSeries (fun u v => jN e f u v r *
      sourceMode e u r*sourceMode f v r-rho e f u v) (jS e f r) := by
    change JointSeries _ (fun p q => mulPoly (jNumerator e f r)
      (fun p q => m e p r*m f q r) p q-rhoTable (e == f) p q)
    simpa only [eval_jNumerator, mul_assoc] using hn
  have hl' : JointSeries (fun u v => jN e f u v r *
      sourceMode e u r*sourceMode f v r-rho e f u v)
      (jStencil (e == f) (fun p q => externalJ e p f q z -
        (Qconstant e f r-k r)*d e f r p q)) := by
    apply hl.congr_disk (S := min (1-‖z‖) (1-‖r‖)) (lt_min (by linarith) (by linarith))
    intro u v hu hv
    have huz : ‖u‖+‖z‖<1 := by have := hu.trans_le (min_le_left _ _); linarith
    have hvz : ‖v‖+‖z‖<1 := by have := hv.trans_le (min_le_left _ _); linarith
    have hur : ‖u‖+‖r‖<1 := by have := hu.trans_le (min_le_right _ _); linarith
    have hvr : ‖v‖+‖r‖<1 := by have := hv.trans_le (min_le_right _ _); linarith
    rw [(OriginalGaussianComplexRadialContinuation.allSignsJT_eq_candidates_complex e f huz hvz).1]
    simpa only [r, OriginalGaussianFiniteCandidateModes.k,
      OriginalGaussianFiniteCandidateModes.ell, OriginalGaussianExternalAnalyticCandidate.correction,
      OriginalGaussianExternalAnalyticCandidate.ell, mul_assoc] using
        OriginalGaussianExternalSignedCandidate.candidateJ_cleared e f hur hvr
  exact hl'.unique hn' (fun _ _ => rfl)

/-- Every natural mode and every sign, including the zero rows and z=0. -/
theorem externalJ_signed_finite_eq (e f : Bool) (p q : ℕ) {z : ℂ} (hz : ‖z‖<1) :
    externalJ e p f q z = jSigned e f p q (z^2) := by
  have he := congrArg (fun S => jInverse (e == f) S p q) (actualJ_stencil e f hz)
  rw [jInverse_stencil] at he
  unfold jSigned
  linear_combination he

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
