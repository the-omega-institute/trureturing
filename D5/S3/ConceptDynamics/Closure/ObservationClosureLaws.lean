/- GID: D5/S3/ConceptDynamics/Closure/ObservationClosureLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Closure/ObservationClosureLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observation closure has the three closure laws and adds no distinctions. -/

import D5.S3.ConceptDynamics.Closure.SourceClosureThreeLaws
import D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion

/- Library-search audit trail (2026-08-28):
   * Exact D5 hit `source_closure_three_laws` supplies the extensive, monotone,
     and idempotent clauses for the canonical `DefinitionClosure`.
   * Exact D5 hit `semantic_closure_zero_gain_criterion` supplies the public
     redundancy clause as equality of the canonical common kernels after a
     candidate readout is inserted.
   * Body-shape searches found `DefinitionClosure`, `SemanticClosure`,
     `jointKernel`, and `jointReadout`; no carrier is redeclared. Pinned Mathlib
     Galois-connection searches found the standard component laws but no
     theorem packaging all four source clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Closure.ObservationClosureLaws

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.Closure.SourceClosureThreeLaws
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion

/-- The canonical observation closure is extensive, monotone, and idempotent.
Every readout in it is distinction-redundant: inserting that readout leaves the
family's common observational kernel unchanged. -/
theorem observation_closure_laws
    {X Output : Type*}
    (sources larger : Set (Concept X Output)) :
    sources ⊆ DefinitionClosure sources /\
      (sources ⊆ larger ->
        DefinitionClosure sources ⊆ DefinitionClosure larger) /\
      DefinitionClosure (DefinitionClosure sources) =
        DefinitionClosure sources /\
      forall candidate : Concept X Output,
        candidate ∈ DefinitionClosure sources ->
          jointKernel
              (fun definition : Set.insert candidate sources => definition.1) =
            jointKernel (fun definition : sources => definition.1) := by
  have laws := source_closure_three_laws sources larger
  refine ⟨laws.1, laws.2.1, laws.2.2, ?_⟩
  intro candidate redundant
  apply (semantic_closure_zero_gain_criterion sources candidate).mp
  exact redundant

#print axioms observation_closure_laws

end D5.S3.ConceptDynamics.Closure.ObservationClosureLaws
