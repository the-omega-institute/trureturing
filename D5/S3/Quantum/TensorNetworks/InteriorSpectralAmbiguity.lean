/- GID: D5/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorSpectralAmbiguity
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Nonzero canonical REAL13 exclusion with the genuine native actual ambiguity consumer. -/

import D5.S3.Quantum.TensorNetworks.InteriorSpectralWitness
import D5.S3.Quantum.TensorNetworks.InteriorSpectralEnvironments

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
open Matrix MvPolynomial
open scoped Matrix
open InteriorSpectralCertificate InteriorSpectralWitness
open OpenBoundaryMPSSpectralExtraction

/-- The literal nonzero lengthwise exclusion certificate has an actual native ambiguity consumer.
Every root e is covered, hence both physical square-root branches. -/
theorem canonical_exclusion_actual_ambiguity (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    P p q ≠ 0 ∧ ∀ (x : Fin 13 → ℝ) (e : ℂ),
      0 < OpenBoundaryMPSQ2PolynomialFiber.sigma x → eval x (P p q) ≠ 0 →
      e^2 = D (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) →
      ∃ φ : PeriodicMPSParentIntersection.Word ((p+2)+q) → ℂ,
        φ ∈ OpenBoundaryMPSMarginalBirationality.openBoundaryMPS ((p+2)+q) ∧ φ ≠ 0 ∧
        OpenBoundaryMPSInteriorCommonCore.rawInterior p 2 q φ =
          OpenBoundaryMPSInteriorCommonCore.rawInterior p 2 q
            (OpenBoundaryMPSMarginalBirationality.mpsState ((p+2)+q)
              (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 0)
              (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 1)
              (L (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x))
              ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
                ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x])) ∧
        ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ = η •
          OpenBoundaryMPSMarginalBirationality.mpsState ((p+2)+q)
            (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 0)
            (A (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) 1)
            (L (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x))
            ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
              ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x]) := by
  refine ⟨P_nonzero p q hp hq,?_⟩
  intro x e hsigma hP he
  obtain ⟨hc,hs,hb⟩ := certificate_native p q x e hsigma hP he
  obtain ⟨hl,hr⟩ := InteriorSpectralEnvironments.certificate_positive_targets
    p q hp hq x e hsigma hP he
  exact canonical_actual_ambiguity_of_native p q hp hq x e
    ((Real.sqrt (OpenBoundaryMPSQ2PolynomialFiber.sigma x) : ℂ) •
      ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x]) hc hs hl hr hb

end D5.S3.Quantum.TensorNetworks.InteriorSpectralAmbiguity
