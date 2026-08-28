/- GID: D5/S3/ConceptDynamics/DecisionValueScale/StrictMonotoneObjectiveArgmaxAlignment
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/StrictMonotoneObjectiveArgmaxAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strictly increasing objective factorization preserves every feasible argmax set. -/

import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-26):
   * Repository searches for `argmax`, objective alignment, strict monotonicity, and
     `IsGreatest` found no D5 theorem stating preservation on an arbitrary feasible set.
   * Body-shape searches for the feasible-set maximizer predicate found no canonical D5
     definition, so the public theorem expands that source predicate instead of adding one.
   * Pinned Mathlib provides the exact order-reflection lemma `StrictMono.le_iff_le` in
     `Mathlib.Order.Monotone.Basic`; it is applied in both directions below. No packaged
     theorem equating the two feasible argmax sets was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.StrictMonotoneObjectiveArgmaxAlignment

/-- If the principal objective is a strictly increasing transform of the agent objective,
the two objectives select exactly the same maximizers on every common feasible set. -/
theorem strict_monotone_factorization_preserves_argmax
    {Z : Type*} (feasible : Set Z)
    (agentObjective principalObjective : Z -> Real)
    (transform : Real -> Real) (strictlyIncreasing : StrictMono transform)
    (factorization : principalObjective = transform ∘ agentObjective) :
    {candidate | candidate ∈ feasible ∧
      ∀ alternative ∈ feasible,
        agentObjective alternative ≤ agentObjective candidate} =
    {candidate | candidate ∈ feasible ∧
      ∀ alternative ∈ feasible,
        principalObjective alternative ≤ principalObjective candidate} := by
  ext candidate
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨candidateFeasible, maximal⟩
    refine ⟨candidateFeasible, ?_⟩
    intro alternative alternativeFeasible
    simpa [factorization] using
      strictlyIncreasing.le_iff_le.mpr (maximal alternative alternativeFeasible)
  · rintro ⟨candidateFeasible, maximal⟩
    refine ⟨candidateFeasible, ?_⟩
    intro alternative alternativeFeasible
    apply strictlyIncreasing.le_iff_le.mp
    simpa [factorization] using maximal alternative alternativeFeasible

#print axioms strict_monotone_factorization_preserves_argmax

end D5.S3.ConceptDynamics.DecisionValueScale.StrictMonotoneObjectiveArgmaxAlignment
