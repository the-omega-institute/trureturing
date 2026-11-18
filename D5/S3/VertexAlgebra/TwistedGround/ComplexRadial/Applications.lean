/- GID: D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All signs and both original Gaussian kernels on the full complex source disk. -/

import D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Transport
import D5.S3.VertexAlgebra.TwistedGround.Signed.Identification
import D5.S3.VertexAlgebra.TwistedGround.PositiveT.GeneratorIdentification

/-! The concrete positive and signed suppliers give all eight original complex radial identities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianComplexRadialContinuation
open OriginalGaussianExternalGeneratedSource

private lemma signedCandidateJ_true_true_eq_positive (u v r : ℂ) :
    OriginalGaussianExternalSignedCandidate.candidateJ true true u v r =
      OriginalGaussianExternalAnalyticCandidate.candidateJ u v r := by
  rfl

private lemma signedCandidateT_true_true_eq_positive (u v r : ℂ) :
    OriginalGaussianExternalSignedCandidate.candidateT true true u v r =
      OriginalGaussianExternalAnalyticCandidate.candidateT u v r := by
  have he : OriginalGaussianExternalSignedCandidate.E true true u v r =
      OriginalGaussianExternalAnalyticCandidate.E u v r := by
    simp only [OriginalGaussianExternalSignedCandidate.E,
      OriginalGaussianExternalSignedCandidate.K, ite_true,
      OriginalGaussianExternalAnalyticCandidate.E, OriginalGaussianExternalAnalyticCandidate.b]
    ring
  simp only [OriginalGaussianExternalSignedCandidate.candidateT,
    OriginalGaussianExternalSignedCandidate.rationalT,
    OriginalGaussianExternalSignedCandidate.N, ite_true, he,
    OriginalGaussianExternalAnalyticCandidate.candidateT,
    OriginalGaussianExternalAnalyticCandidate.rationalT]

/-- The positive J instance consumes the actual real radial identification. -/
theorem positiveJ_eq_candidateJ_complex {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode false true true u v z =
      OriginalGaussianExternalSignedCandidate.candidateJ true true u v (z ^ 2) := by
  apply kernelMode_eq_candidate_complex_of_real false true true _ hu hv
  intro r hr hr1 hur hvr
  change kernelMode false true true u v (Real.sqrt r : ℂ) =
    OriginalGaussianExternalSignedCandidate.candidateJ true true u v (r : ℂ)
  rw [signedCandidateJ_true_true_eq_positive]
  exact OriginalGaussianExternalAnalyticCandidate.positiveJ_eq_candidateJ hr hr1 hur hvr

/-- Only a sign restriction in addition to the original domain; no public
analyticity, PDE, summability or nonzero hypothesis. -/
theorem signedJ_eq_candidateJ_complex (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1)
    (hneg : e = false ∨ f = false) :
    kernelMode false e f u v z =
      OriginalGaussianExternalSignedCandidate.candidateJ e f u v (z ^ 2) := by
  apply kernelMode_eq_candidate_complex_of_real false e f _ hu hv
  intro r hr hr1 hur hvr
  exact OriginalGaussianSignedIdentification.signedJ_eq_candidateJ
    e f hr hr1 hur hvr hneg

/-- All four J sign sectors on the original complex source domain. -/
theorem allSignsJ_eq_candidateJ_complex (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode false e f u v z =
      OriginalGaussianExternalSignedCandidate.candidateJ e f u v (z ^ 2) := by
  cases e <;> cases f
  · exact signedJ_eq_candidateJ_complex false false hu hv (Or.inl rfl)
  · exact signedJ_eq_candidateJ_complex false true hu hv (Or.inl rfl)
  · exact signedJ_eq_candidateJ_complex true false hu hv (Or.inr rfl)
  · exact positiveJ_eq_candidateJ_complex hu hv

/-- The three negative-label T sectors use the actual named real consumer. -/
theorem signedT_eq_candidateT_complex (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1)
    (hneg : e = false ∨ f = false) :
    kernelMode true e f u v z =
      OriginalGaussianExternalSignedCandidate.candidateT e f u v (z ^ 2) := by
  apply kernelMode_eq_candidate_complex_of_real true e f _ hu hv
  intro r hr hr1 hur hvr
  exact OriginalGaussianSignedIdentification.signedT_eq_candidateT
    e f hr hr1 hur hvr hneg

/-- The positive T instance consumes the actual generating-kernel supplier. -/
theorem positiveT_eq_candidateT_complex {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode true true true u v z =
      OriginalGaussianExternalSignedCandidate.candidateT true true u v (z ^ 2) := by
  apply kernelMode_eq_candidate_complex_of_real true true true _ hu hv
  intro r hr hr1 hur hvr
  change kernelMode true true true u v (Real.sqrt r : ℂ) =
    OriginalGaussianExternalSignedCandidate.candidateT true true u v (r : ℂ)
  rw [signedCandidateT_true_true_eq_positive]
  exact PositiveT.GeneratorIdentification.positiveT_eq_candidateT hr hr1 hur hvr

/-- All four T sign sectors on the original complex source domain. -/
theorem allSignsT_eq_candidateT_complex (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode true e f u v z =
      OriginalGaussianExternalSignedCandidate.candidateT e f u v (z ^ 2) := by
  cases e <;> cases f
  · exact signedT_eq_candidateT_complex false false hu hv (Or.inl rfl)
  · exact signedT_eq_candidateT_complex false true hu hv (Or.inl rfl)
  · exact signedT_eq_candidateT_complex true false hu hv (Or.inr rfl)
  · exact positiveT_eq_candidateT_complex hu hv

/-- Both literal original kernels equal their signed candidates for all signs
and every complex radial parameter in the original source norm domain. -/
theorem allSignsJT_eq_candidates_complex (e f : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode false e f u v z =
        OriginalGaussianExternalSignedCandidate.candidateJ e f u v (z ^ 2) ∧
      kernelMode true e f u v z =
        OriginalGaussianExternalSignedCandidate.candidateT e f u v (z ^ 2) := by
  exact ⟨allSignsJ_eq_candidateJ_complex e f hu hv,
    allSignsT_eq_candidateT_complex e f hu hv⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianComplexRadialContinuation
