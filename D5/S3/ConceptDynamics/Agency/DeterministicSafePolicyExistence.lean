/- GID: D5/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/DeterministicSafePolicyExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fiberwise safe actions characterize deterministic observation-based safe policies. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-27):
   * Repository searches for safe policies, fiber intersections, `Set.range q`,
     and observation-based selectors found no exact D5 declaration.
   * Body-shape searches for a policy on `Set.range q` that is legal at every
     compatible full state found no canonical D5 primitive.
   * Pinned Mathlib supplies dependent choice through `Classical.choose`, but
     no packaged theorem states this fiberwise safety equivalence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.DeterministicSafePolicyExistence

/-- A deterministic policy on the effective observation carrier is safe at
every compatible full state exactly when every effective observation fiber has
a common legal action. This is the set-theoretic statement; no measurable
selector is asserted. -/
theorem deterministic_safe_policy_exists_iff
    {X Q A : Type*} (q : X -> Q) (legal : X -> Set A) :
    (exists policy : Set.range q -> A,
      forall z x, q x = z.1 -> policy z ∈ legal x) ↔
      forall z : Set.range q,
        ({action | forall x, q x = z.1 -> action ∈ legal x} : Set A).Nonempty := by
  constructor
  · rintro ⟨policy, safe⟩ z
    exact ⟨policy z, fun x hx => safe z x hx⟩
  · intro fiberNonempty
    classical
    choose policy safe using fiberNonempty
    exact ⟨policy, fun z x hx => safe z x hx⟩

#print axioms deterministic_safe_policy_exists_iff

end D5.S3.ConceptDynamics.Agency.DeterministicSafePolicyExistence
