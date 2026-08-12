/- GID: D5/S3/QuantumContext/ClassicalAddressRealismExclusion
   generality: I
   mirror-B: D5/B/S3/QuantumContext/ClassicalAddressRealismExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite projection contexts exclude a global classical assignment. -/

/- Library-search audit trail (2026-08-13):
   * The pinned mathlib tree was searched for finite-image cardinality and finite-sum support
     lemmas. `Finset.card_image_of_injective` supplies the context-cardinality witness, while
     ordinary `Finset` simplification verifies the one-context assignment.
   * The frozen `projection_valuation_obstruction` theorem supplies the contradiction on the
     eighteen actual projections. This module only gives that result the requested classical
     address-realistic presentation and does not reprove its parity certificate.
-/

import D5.S3.QuantumContext.ProjectionValuationObstruction

/-!
# Classical address realism on the finite projection configuration

Here a classical address-realistic model assigns a definite binary outcome to each of the
eighteen ray labels at every hidden address, with exactly one selected outcome in every displayed
context. The exclusion below is limited to this explicit finite configuration.
-/

namespace D5.S3.QuantumContext.ClassicalAddressRealismExclusion

open D5.S3.QuantumContext.ProjectionValuationObstruction
open scoped BigOperators

/-- A deterministic hidden-address model for the eighteen displayed ray labels. -/
structure ClassicalAddressRealism where
  Address : Type
  address_nonempty : Nonempty Address
  outcome : Address → Fin 18 → Fin 2
  context_complete : ∀ address : Address, ∀ c : Fin 9,
    ∑ k : Fin 4, (outcome address (contextRay c k)).val = 1

/-- The ray label chosen for an actual projection in the finite configuration. -/
noncomputable def projectionLabel (P : ConfigurationProjection) : Fin 18 :=
  Classical.choose P.property

theorem projectionLabel_spec (P : ConfigurationProjection) :
    labeledProjection (projectionLabel P) = P := by
  apply Subtype.ext
  exact Classical.choose_spec P.property

theorem projectionLabel_labeledProjection (r : Fin 18) :
    projectionLabel (labeledProjection r) = r := by
  apply labeledProjection_injective
  exact projectionLabel_spec (labeledProjection r)

/-- The valuation on actual projections induced by one hidden address. -/
noncomputable def inducedProjectionValuation
    (realism : ClassicalAddressRealism) (address : realism.Address) :
    ConfigurationProjection → Fin 2 :=
  fun P ↦ realism.outcome address (projectionLabel P)

theorem address_induces_global_projection_valuation
    (realism : ClassicalAddressRealism) (address : realism.Address) :
    ∃ value : ConfigurationProjection → Fin 2,
      ∀ c : Fin 9,
        ∑ k : Fin 4, (value (labeledProjection (contextRay c k))).val = 1 := by
  refine ⟨inducedProjectionValuation realism address, ?_⟩
  intro c
  simpa [inducedProjectionValuation, projectionLabel_labeledProjection] using
    realism.context_complete address c

/-- The finite set of actual projections displayed in one context. -/
noncomputable def projectionContext (c : Fin 9) : Finset ConfigurationProjection :=
  Finset.univ.image fun k ↦ labeledProjection (contextRay c k)

/-- The displayed context family is inhabited. -/
theorem projection_contexts_nonempty : Nonempty (Fin 9) := ⟨0⟩

/-- Every displayed context contains four distinct actual projections. -/
theorem context_projections_card_four (c : Fin 9) : (projectionContext c).card = 4 := by
  classical
  calc
    (projectionContext c).card = (Finset.univ : Finset (Fin 4)).card := by
      apply Finset.card_image_of_injective
      intro a b h
      exact contextRay_injective c (labeledProjection_injective h)
    _ = 4 := by simp

/-- A binary value selecting the first projection of the first context. -/
noncomputable def firstContextAssignment (P : ConfigurationProjection) : Fin 2 :=
  if P = labeledProjection (contextRay 0 0) then 1 else 0

/-- The explicit local assignment selects exactly one projection in the first context. -/
theorem first_context_assignment_satisfies :
    ∑ k : Fin 4, (firstContextAssignment (labeledProjection (contextRay 0 k))).val = 1 := by
  classical
  have heq (k : Fin 4) :
      labeledProjection (contextRay 0 k) = labeledProjection (contextRay 0 0) ↔ k = 0 := by
    constructor
    · intro h
      exact contextRay_injective 0 (labeledProjection_injective h)
    · rintro rfl
      rfl
  simp [firstContextAssignment, heq, Fin.sum_univ_succ]

/-- The explicit eight-context assignment is a genuine near miss: it satisfies the first eight
contexts, but no assignment extending it can satisfy all nine. -/
theorem eight_context_near_miss_cannot_extend :
    ∃ value : Fin 18 → Fin 2,
      (∀ c : Fin 9, c.val < 8 →
        ∑ k : Fin 4, (value (contextRay c k)).val = 1) ∧
      ¬ (∀ c : Fin 9,
        ∑ k : Fin 4, (value (contextRay c k)).val = 1) := by
  refine ⟨eightContextValuation, eight_contexts_satisfiable, ?_⟩
  intro hvalue
  exact nine_context_parity_contradiction eightContextValuation hvalue

/-- The obstruction is global rather than vacuous: contexts exist, each has four distinct
projections, and the first context alone has an explicit satisfying binary assignment. -/
theorem projection_configuration_is_nonvacuous :
    Nonempty (Fin 9) ∧
      (∀ c : Fin 9, (projectionContext c).card = 4) ∧
      ∃ value : ConfigurationProjection → Fin 2,
        ∑ k : Fin 4, (value (labeledProjection (contextRay 0 k))).val = 1 := by
  exact ⟨projection_contexts_nonempty, context_projections_card_four, firstContextAssignment,
    first_context_assignment_satisfies⟩

/-- No deterministic classical hidden-address model exists for the finite projection configuration.
The bridge above supplies the frozen obstruction with a global valuation induced by any address. -/
theorem classical_address_realism_exclusion :
    ¬ Nonempty ClassicalAddressRealism := by
  rintro ⟨realism⟩
  obtain ⟨address⟩ := realism.address_nonempty
  exact projection_valuation_obstruction
    (address_induces_global_projection_valuation realism address)

end D5.S3.QuantumContext.ClassicalAddressRealismExclusion
