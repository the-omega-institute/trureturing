/- GID: D5/S3/ConceptDynamics/Faithfulness/BareValueObservationNoninjective
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/BareValueObservationNoninjective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A value-only observation identifies distinct structural completion certificates. -/

import D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches found the exact Gaussian completion theorem
     `gaussian_self_dual_iff`; it is imported and applied below. The related
     observation-topology modules assume noninjectivity or prove its downstream
     consequences, so they do not cover this certificate projection.
   * Pinned Mathlib supplies the exact logical witness equivalence
     `Function.not_injective_iff` and the rotation identity
     `Complex.exp_pi_mul_I`; both are applied below.
   * Loogle returned `Function.not_injective_iff` exactly. LeanSearch and
     Reservoir API probes returned HTTP 404, while unauthenticated GitHub code
     search returned HTTP 401. No third-party certificate theorem was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.BareValueObservationNoninjective

open MeasureTheory
open scoped FourierTransform

open D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi

noncomputable section

/-- The two completion problems used by the source counterexample. -/
inductive CompletionProblem where
  | gaussianFourierSelfDual
  | rotationHalfPeriod
deriving DecidableEq

/-- The candidate object space depends on the structural completion role. -/
def objectSpace : CompletionProblem -> Type
  | .gaussianFourierSelfDual => ℝ -> ℂ
  | .rotationHalfPeriod => ℂ

/-- The positive real Gaussian at scale `a`, in the complex Fourier codomain. -/
def gaussianAt (a : ℝ) : ℝ -> ℂ :=
  fun x => (Real.exp (-a * x ^ 2) : ℂ)

/-- The completion equation belonging to each of the two structural roles. -/
def CompletionEquation : CompletionProblem -> ℂ -> Prop
  | .gaussianFourierSelfDual, kappa =>
      exists a : ℝ, 0 < a /\ kappa = (a : ℂ) /\ 𝓕 (gaussianAt a) = gaussianAt a
  | .rotationHalfPeriod, kappa =>
      kappa = (Real.pi : ℂ) /\ Complex.exp (kappa * Complex.I) = -1

/-- A constant certificate retains its completion problem and evidence, while
`val` below deliberately returns only its complex number. -/
structure ConstCert where
  problem : CompletionProblem
  value : ℂ
  isCompletion : CompletionEquation problem value

/-- The bare numerical observation on constant certificates. -/
def val (certificate : ConstCert) : ℂ := certificate.value

/-- The Gaussian Fourier self-dual completion certificate at scale `pi`. -/
def gaussianFourierCertificate : ConstCert where
  problem := .gaussianFourierSelfDual
  value := Real.pi
  isCompletion := by
    refine ⟨Real.pi, Real.pi_pos, rfl, ?_⟩
    change
      𝓕 (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) =
        (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ))
    exact (gaussian_self_dual_iff Real.pi Real.pi_pos).2 rfl

/-- The rotation half-period completion certificate at angle `pi`. -/
def rotationHalfPeriodCertificate : ConstCert where
  problem := .rotationHalfPeriod
  value := Real.pi
  isCompletion := by
    refine ⟨rfl, ?_⟩
    exact Complex.exp_pi_mul_I

/-- Forgetting the completion role and returning only its numerical value is
not injective: the Gaussian and rotation certificates both return `pi`. -/
theorem bare_value_observation_not_injective :
    Not (Function.Injective val) := by
  apply Function.not_injective_iff.mpr
  refine ⟨gaussianFourierCertificate, rotationHalfPeriodCertificate, rfl, ?_⟩
  intro certificatesEqual
  have problemsEqual := congrArg ConstCert.problem certificatesEqual
  exact CompletionProblem.noConfusion problemsEqual

/-- Reverse probe: the public proposition exposes a genuine collision of two
distinct structural certificates. -/
example :
    exists first second : ConstCert,
      val first = val second /\ first ≠ second :=
  Function.not_injective_iff.mp bare_value_observation_not_injective

/-- Trivialization probe: a singleton certificate carrier makes every value
observation injective, so it cannot satisfy the public theorem. -/
example (f : Unit -> ℂ) : Function.Injective f := by
  intro first second _
  exact Subsingleton.elim first second

#print axioms bare_value_observation_not_injective

end

end D5.S3.ConceptDynamics.Faithfulness.BareValueObservationNoninjective
