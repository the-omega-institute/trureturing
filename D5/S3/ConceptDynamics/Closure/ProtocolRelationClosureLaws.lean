/- GID: D5/S3/ConceptDynamics/Closure/ProtocolRelationClosureLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Closure/ProtocolRelationClosureLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Protocol definition and relation closures satisfy the three closure laws. -/

import D5.S3.ConceptDynamics.Closure.SourceClosureThreeLaws

/- Library-search audit trail (2026-08-28):
   * Body-shape searches found the canonical `DefinitionClosure`,
     `RelationInvariantReadouts`, and `jointKernel` in
     `DefinitionKernelGalois`; they are imported rather than redeclared.
   * Exact frozen D5 hit `source_closure_three_laws` supplies the three
     protocol-family clauses. No frozen theorem packages the corresponding
     three laws for `jointKernel` of all relation-invariant readouts.
   * Pinned Mathlib set-lattice lemmas are sufficient for the relation-side
     subset arguments; no exact six-clause theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Closure.ProtocolRelationClosureLaws

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/-- The protocol closure `Pi (K Q)` and the relation closure `K (Pi R)`,
constructed from the canonical Galois primitives, are both extensive,
monotone, and idempotent. -/
theorem protocol_relation_closure_laws
    {X Output : Type*}
    (sources larger : Set (Concept X Output))
    (relation largerRelation : Set (X × X)) :
    sources ⊆ DefinitionClosure sources ∧
      (sources ⊆ larger →
        DefinitionClosure sources ⊆ DefinitionClosure larger) ∧
      DefinitionClosure (DefinitionClosure sources) =
        DefinitionClosure sources ∧
      relation ⊆
        jointKernel
          (fun readout : RelationInvariantReadouts (Output := Output) relation =>
            readout.1) ∧
      (relation ⊆ largerRelation →
        jointKernel
            (fun readout : RelationInvariantReadouts (Output := Output) relation =>
              readout.1) ⊆
          jointKernel
            (fun readout : RelationInvariantReadouts
              (Output := Output) largerRelation => readout.1)) ∧
      jointKernel
          (fun readout : RelationInvariantReadouts (Output := Output)
            (jointKernel
              (fun readout : RelationInvariantReadouts
                (Output := Output) relation => readout.1)) =>
            readout.1) =
        jointKernel
          (fun readout : RelationInvariantReadouts (Output := Output) relation =>
            readout.1) := by
  refine ⟨definitionClosure_extensive sources,
    fun subset => definitionClosure_mono subset,
    definitionClosure_idempotent sources, ?_, ?_, ?_⟩
  · intro pair pairInRelation
    apply Set.mem_iInter.2
    intro readout
    exact readout.2 pairInRelation
  · intro relationSubset
    apply jointKernel_antitone (X := X) (Output := Output)
    intro readout invariantOnLarger
    intro left right pairInRelation
    exact invariantOnLarger (relationSubset pairInRelation)
  · apply Set.Subset.antisymm
    · apply jointKernel_antitone (X := X) (Output := Output)
      intro readout invariantOnRelation
      intro left right pairInClosedRelation
      exact Set.mem_iInter.1 pairInClosedRelation
        ⟨readout, invariantOnRelation⟩
    · intro pair pairInClosedRelation
      apply Set.mem_iInter.2
      intro readout
      exact readout.2 (by simpa only [Prod.eta] using pairInClosedRelation)

#print axioms protocol_relation_closure_laws

end D5.S3.ConceptDynamics.Closure.ProtocolRelationClosureLaws
