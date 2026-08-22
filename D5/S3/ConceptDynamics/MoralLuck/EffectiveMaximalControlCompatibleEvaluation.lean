/- GID: D5/S3/ConceptDynamics/MoralLuck/EffectiveMaximalControlCompatibleEvaluation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/MoralLuck/EffectiveMaximalControlCompatibleEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical common coarsening is the maximal control-compatible evaluation. -/

import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

/- Library-search audit trail (2026-08-22):
   * Exact family hits `EffectiveConcept`, `effective_refines_iff_reverse_kernel`,
     and `commonCoarsening` are imported from `ConceptKernelOrderDuality`.
   * Exact pinned-Mathlib hits `Setoid.ker_mk_eq`, `Quotient.mk_surjective`,
     `le_sup_left`, `le_sup_right`, and `sup_le` supply the quotient and lattice proof.
   * Repository searches for a maximal control-compatible common coarsening found
     only a frozen predecessor with an extra inhabitedness assumption; no exact
     theorem matching the effective-quotient source context was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.MoralLuck.EffectiveMaximalControlCompatibleEvaluation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

universe u

/-- The canonical common coarsening of an effective evaluation and control
readout refines both, and every effective common coarsening refines it. -/
theorem maximal_control_compatible_evaluation
    {X : Type u} (evaluation control candidate : EffectiveConcept X) :
    Refines
        (commonCoarsening evaluation.readout control.readout)
        evaluation.readout ∧
      Refines
        (commonCoarsening evaluation.readout control.readout)
        control.readout ∧
      ((Refines candidate.readout evaluation.readout ∧
          Refines candidate.readout control.readout) →
        Refines candidate.readout
          (commonCoarsening evaluation.readout control.readout)) := by
  let fair : EffectiveConcept X :=
    { Coordinate := Quotient
        (Setoid.ker evaluation.readout ⊔ Setoid.ker control.readout)
      readout := commonCoarsening evaluation.readout control.readout
      effective := Quotient.mk_surjective }
  constructor
  · apply (effective_refines_iff_reverse_kernel fair evaluation).2
    change Setoid.ker evaluation.readout ≤
      Setoid.ker (commonCoarsening evaluation.readout control.readout)
    rw [commonCoarsening, Setoid.ker_mk_eq]
    exact le_sup_left
  constructor
  · apply (effective_refines_iff_reverse_kernel fair control).2
    change Setoid.ker control.readout ≤
      Setoid.ker (commonCoarsening evaluation.readout control.readout)
    rw [commonCoarsening, Setoid.ker_mk_eq]
    exact le_sup_right
  · rintro ⟨hEvaluation, hControl⟩
    apply (effective_refines_iff_reverse_kernel candidate fair).2
    change Setoid.ker (commonCoarsening evaluation.readout control.readout) ≤
      Setoid.ker candidate.readout
    rw [commonCoarsening, Setoid.ker_mk_eq]
    exact sup_le
      ((effective_refines_iff_reverse_kernel candidate evaluation).1 hEvaluation)
      ((effective_refines_iff_reverse_kernel candidate control).1 hControl)

/-- The theorem remains available when the source carrier is empty. -/
example :
    let emptyConcept : EffectiveConcept Empty :=
      { Coordinate := Empty
        readout := id
        effective := Function.surjective_id }
    Refines
        (commonCoarsening emptyConcept.readout emptyConcept.readout)
        emptyConcept.readout ∧
      Refines
        (commonCoarsening emptyConcept.readout emptyConcept.readout)
        emptyConcept.readout ∧
      ((Refines emptyConcept.readout emptyConcept.readout ∧
          Refines emptyConcept.readout emptyConcept.readout) →
        Refines emptyConcept.readout
          (commonCoarsening emptyConcept.readout emptyConcept.readout)) := by
  dsimp only
  exact maximal_control_compatible_evaluation
    ({ Coordinate := Empty
       readout := id
       effective := Function.surjective_id } : EffectiveConcept Empty)
    ({ Coordinate := Empty
       readout := id
       effective := Function.surjective_id } : EffectiveConcept Empty)
    ({ Coordinate := Empty
       readout := id
       effective := Function.surjective_id } : EffectiveConcept Empty)

/-- The grouped maximality premises are jointly satisfiable in a two-state model. -/
example :
    let identityConcept : EffectiveConcept Bool :=
      { Coordinate := Bool
        readout := id
        effective := Function.surjective_id }
    Refines identityConcept.readout identityConcept.readout ∧
      Refines identityConcept.readout identityConcept.readout := by
  dsimp only
  exact ⟨⟨id, rfl⟩, ⟨id, rfl⟩⟩

#print axioms maximal_control_compatible_evaluation

end D5.S3.ConceptDynamics.MoralLuck.EffectiveMaximalControlCompatibleEvaluation
