/- GID: D5/S3/ConceptDynamics/BlindNaturalityCountermodel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/BlindNaturalityCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A constant readout can commute with a process while losing target distinctions. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-21):
   * Searches of D5, the active frozen ledger, and the source vocabulary for
     blind naturality, constant readouts, and target-faithfulness countermodels
     found no exact theorem.
   * Exact repository hits `ConceptFiberDecomposition.Concept` and
     `ConceptJoinUniversal.Refines` are the canonical family primitives and are
     imported and applied directly; no sibling readout or factor relation is
     declared here.
   * Pinned Mathlib's `Function.comp_apply` and `congrArg` are the direct
     equality-transport tools used in the factor contradiction. No library
     theorem packages the required existential countermodel.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.BlindNaturalityCountermodel

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A one-point readout admits a strictly commuting macro square for a process,
while a nonconstant target cannot factor through that readout. -/
theorem blind_naturality_counterexample :
    ∃ (readout : Concept Bool Unit) (process : Bool -> Bool)
      (target : Concept Bool Bool),
      (∃ induced : Unit -> Unit,
        readout ∘ process = induced ∘ readout) ∧
      ¬Refines target readout := by
  refine ⟨fun _ => (), id, id, ?_, ?_⟩
  · exact ⟨id, by funext state; rfl⟩
  · rintro ⟨factor, hfactor⟩
    have hfalse := congrFun hfactor false
    have htrue := congrFun hfactor true
    have impossible : false = true := hfalse.trans htrue.symm
    exact Bool.false_ne_true impossible

/-- The constant readout, identity process, and identity target are concrete
inhabited source objects; the target separates the two Boolean states. -/
example :
    ∃ (readout : Concept Bool Unit) (process : Bool -> Bool)
      (target : Concept Bool Bool),
      (∃ induced : Unit -> Unit,
        readout ∘ process = induced ∘ readout) ∧
      ¬Refines target readout := blind_naturality_counterexample

#print axioms blind_naturality_counterexample

end D5.S3.ConceptDynamics.BlindNaturalityCountermodel
