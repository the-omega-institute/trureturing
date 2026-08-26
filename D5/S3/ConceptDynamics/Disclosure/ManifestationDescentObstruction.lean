/- GID: D5/S3/ConceptDynamics/Disclosure/ManifestationDescentObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Disclosure/ManifestationDescentObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A newly visible distinction obstructs descent through the current public readout. -/

import D5.S3.ConceptDynamics.RefinementFactorization.RefinementShrinksIndistinguishability

/- Library-search audit trail (2026-08-26):
   * `NoninterferenceSecretFlowExclusion` is the closest frozen D5 theorem, but
     it adds a hidden readout and hidden-value inequality and excludes a global
     existential witness under an assumed refinement. Source theorem 9.1 fixes
     one pair and directly denies the descent map, so that theorem is not an
     exact bind target.
   * Exact D5 hits `Refines` and
     `refinement_shrinks_indistinguishability` provide the canonical descent
     predicate and its equality-transport consequence and are reused here.
   * Pinned Mathlib supplies `Function.FactorsThrough` and
     `Function.factorsThrough_iff`, but `Refines` is the established D5 owner
     of the source equation. No pinned theorem packages this pairwise
     obstruction on the program-flow composite. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Disclosure.ManifestationDescentObstruction

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.RefinementFactorization.RefinementShrinksIndistinguishability

universe u v w x

/-- Equal current public readouts together with unequal future public readouts
rule out every descent of the future readout through the current interface. -/
theorem manifestation_excludes_noninterference_descent
    {State : Type u} {CurrentPublic : Type v}
    {FutureState : Type w} {FuturePublic : Type x}
    (low : State -> CurrentPublic)
    (flow : State -> FutureState)
    (output : FutureState -> FuturePublic)
    (stateAA stateAB : State)
    (sameCurrent : low stateAA = low stateAB)
    (differentFuture : output (flow stateAA) ≠ output (flow stateAB)) :
    ¬Refines (output ∘ flow) low := by
  intro descent
  apply differentFuture
  exact refinement_shrinks_indistinguishability
    (output ∘ flow) low descent sameCurrent

#print axioms manifestation_excludes_noninterference_descent

end D5.S3.ConceptDynamics.Disclosure.ManifestationDescentObstruction
