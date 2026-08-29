/- GID: D5/S3/Observer/Agency/Self/AgencyCompletionMinimality
   generality: G
   mirror-B: D5/B/S3/Observer/Agency/Self/AgencyCompletionMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Componentwise recoverability induces recoverability of the paired agency completion. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * The statement is formulated over arbitrary types and functions.
   * Pinned Mathlib supplies only the elementary logical and function facts
     used below.
   * No finiteness, decidable equality, topology, probability, or algebraic
     structure is assumed unless it occurs explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Agency.Self.AgencyCompletionMinimality

universe u v w z

/-- If both the current observer state and the strategy profile factor through
a summary, then their paired agency completion factors through the same
summary. -/
theorem paired_completion_factors_through_summary
    {History : Type u} {Memory : Type v} {Profile : Type w}
    {Summary : Type z}
    (current : History -> Memory) (profile : History -> Profile)
    (summary : History -> Summary)
    (currentFactor : Summary -> Memory)
    (profileFactor : Summary -> Profile)
    (currentFactors : forall h, current h = currentFactor (summary h))
    (profileFactors : forall h, profile h = profileFactor (summary h)) :
    exists pairFactor : Summary -> Memory × Profile,
      (fun h => (current h, profile h)) = pairFactor ∘ summary := by
  refine ⟨fun s => (currentFactor s, profileFactor s), ?_⟩
  funext h
  simp only [Function.comp_apply]
  rw [currentFactors h, profileFactors h]

/-- Each component of the paired completion is recovered by a canonical
projection. -/
theorem paired_completion_recovers_components
    {History : Type u} {Memory : Type v} {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile) :
    (fun h => (current h, profile h).1) = current ∧
      (fun h => (current h, profile h).2) = profile := by
  constructor <;> rfl

#print axioms paired_completion_factors_through_summary
#print axioms paired_completion_recovers_components

end D5.S3.Observer.Agency.Self.AgencyCompletionMinimality
