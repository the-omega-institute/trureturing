/- GID: D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Checked affine presentations reduce original causal witness support budgets while preserving all LP rows and the exact endpoint; certified residual widths transfer strict query decisions. -/

import D5.S0.Certificates.RationalMomentQueryEnvelope
import D5.S3.ConceptDynamics.CausalMoments.CertifiedSparseCausalWitness

/- This consumes the original coefficient array and returns a law on the same
   original causal atom carrier. The affine presentation gives a certified
   dimension upper bound, not an assertion of exact affine rank. Residual
   enclosures concern additional queries; they do not imply that their exact
   identified sets have been preserved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.RankAdaptiveSparseCausalWitness

open scoped BigOperators
open D5.S0.Certificates.RationalFarkas
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalMomentElimination
open D5.S0.Certificates.RationalMomentReplay
open D5.S0.Certificates.RationalAffineMomentCompression
open D5.S0.Certificates.RationalMomentQueryEnvelope
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.CertifiedSparseCausalWitness

/-- A checked affine presentation of all original data rows and the target
returns an equivalent original-carrier witness with support at most r+1. -/
theorem checked_affine_causal_witness {n m r : Nat}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (query : Fin n → ℚ)
    (law : FiniteResponseLaw (Fin n)) (result : Fin n → ℚ)
    (presentation : AffinePresentation (m + 1) r) (steps : List (EliminationStep n))
    (feasible : LinearFeasible A b law.mass)
    (accepted : checkAffineCompression (rowQueryArray A query) law.mass presentation steps = some result) :
    ∃ sparse : FiniteResponseLaw (Fin n), sparse.mass = result ∧
      activeAtoms sparse.mass ⊆ activeAtoms law.mass ∧
      (activeAtoms sparse.mass).card ≤ r + 1 ∧
      LinearFeasible A b sparse.mass ∧
      linearObjective query sparse.mass = linearObjective query law.mass := by
  obtain ⟨hn, ht, hs, hc, hm⟩ :=
    checkAffineCompression_sound (rowQueryArray A query) law.mass result presentation steps accepted
  let sparse : FiniteResponseLaw (Fin n) := ⟨result, hn, ht⟩
  refine ⟨sparse, rfl, hs, hc, ?_, ?_⟩
  · intro c
    have row_eq : linearObjective (A c) result = linearObjective (A c) law.mass := by
      simpa only [rowQueryArray, Fin.cases_succ] using hm c.succ
    change linearObjective (A c) result ≤ b c
    rw [row_eq]
    exact feasible c
  · simpa only [rowQueryArray, Fin.cases_zero] using hm 0

/-- The smaller checked support budget is compatible with the existing exact
lower dual certificate. The original inequality system is unchanged. -/
theorem checked_affine_lower_endpoint {n m r : Nat}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (query : Fin n → ℚ) (lower : ℚ)
    (dual : LowerBoundCertificate A b query lower)
    (law : FiniteResponseLaw (Fin n)) (feasible : LinearFeasible A b law.mass)
    (attains : linearObjective query law.mass = lower)
    (result : Fin n → ℚ) (presentation : AffinePresentation (m + 1) r)
    (steps : List (EliminationStep n))
    (accepted : checkAffineCompression (rowQueryArray A query) law.mass presentation steps = some result) :
    IsExactLowerBound A b query lower ∧
      ∃ sparse : FiniteResponseLaw (Fin n), sparse.mass = result ∧
        (activeAtoms sparse.mass).card ≤ r + 1 ∧
        LinearFeasible A b sparse.mass ∧ linearObjective query sparse.mass = lower := by
  obtain ⟨sparse, equal, _, small, feasible', value⟩ :=
    checked_affine_causal_witness A b query law result presentation steps feasible accepted
  have attains' := value.trans attains
  have witness : PrimalWitness A b query lower := ⟨sparse.mass, feasible', attains'⟩
  exact ⟨exact_lower_bound_of_certificate_and_witness A b query lower dual witness,
    sparse, equal, small, feasible', attains'⟩

/-- A compressed omitted query can certify the original strict decision when
its margin exceeds the checked residual oscillation. This is a deterministic
finite-model guarantee, not a sampling confidence interval. -/
theorem checked_compressed_query_decision {n d : Nat}
    (feature : Fin n → Fin d → ℚ) (weight result query : Fin n → ℚ)
    (steps : List (EliminationStep n)) (envelope : QueryEnvelope d) (threshold : ℚ)
    (accepted : checkCompression feature weight steps = some result)
    (certified : checkQueryEnvelope feature weight query envelope = true)
    (margin : threshold + (envelope.upper - envelope.lower) < linearObjective query result) :
    threshold < linearObjective query weight := by
  have error := checked_query_error_bound feature weight result query steps envelope accepted certified
  have upper := (abs_le.mp error).2
  linarith

#print axioms checked_affine_causal_witness
#print axioms checked_affine_lower_endpoint
#print axioms checked_compressed_query_decision

end D5.S3.ConceptDynamics.CausalMoments.RankAdaptiveSparseCausalWitness
