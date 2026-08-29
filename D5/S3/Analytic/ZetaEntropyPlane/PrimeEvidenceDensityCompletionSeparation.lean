/- GID: D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceDensityCompletionSeparation
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceDensityCompletionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime coordinate count and cumulative evidence admit distinct convergence behaviors. -/

import D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality
import D5.S3.TotalVariation.Asymptotics.WeakPrimeEvidenceFiniteTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceDensityCompletionSeparation

open Filter
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open D5.S3.Analytic.ZetaEntropyPlane.PrimeDensityEvidenceOrthogonality
open D5.S3.TotalVariation.Asymptotics.WeakPrimeEvidenceFiniteTotal

noncomputable section

/-- Prime-coordinate cardinality and cumulative evidence are independent completion signals. -/
theorem prime_evidence_density_completion_separation :
    (Infinite Nat.Primes ∧
      ((∀ p : Nat.Primes,
          0 < -Real.log (D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
            (D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder.positiveBiasLaw
              ((p : Real) ^ (-2 : Real)))
            (D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder.negativeBiasLaw
              ((p : Real) ^ (-2 : Real))))) ∧
        (Summable (fun p : Nat.Primes =>
            -Real.log (D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
              (D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder.positiveBiasLaw
                ((p : Real) ^ (-2 : Real)))
              (D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder.negativeBiasLaw
                ((p : Real) ^ (-2 : Real))))) ∧
          Tendsto (fun p : Nat.Primes =>
            -Real.log (D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
              (D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder.positiveBiasLaw
                ((p : Real) ^ (-2 : Real)))
              (D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder.negativeBiasLaw
                ((p : Real) ^ (-2 : Real)))))
            cofinite (nhds 0)))) ∧
    (Tendsto (naturalCountingRatio primeNaturals) atTop (nhds 0) ∧
      ¬ Summable (restrictedPrimeEvidence primeNaturals 1)) ∧
    (((∀ p : Nat.Primes, p.1 ∈ primeNaturals) ∧
        Summable (restrictedPrimeEvidence primeNaturals 2)) ∧
      (Tendsto (naturalCountingRatio (∅ : Set ℕ)) atTop (nhds 0) ∧
        Summable (restrictedPrimeEvidence (∅ : Set ℕ) 1))) := by
  letI : Infinite Nat.Primes := Nat.infinite_setOf_prime.to_subtype
  have hweak := weak_prime_evidence_finite_total
  have hsparse := sparse_prime_support_diverges
  have hcount := counting_density_not_sufficient_for_summability
  rcases hweak with ⟨hpositive, hsum, hlimit⟩
  exact ⟨⟨inferInstance, hpositive, hsum, hlimit⟩,
    hsparse,
    ⟨hcount.2.1, hcount.2.2⟩⟩

#print axioms prime_evidence_density_completion_separation

end

end D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceDensityCompletionSeparation
