/- GID: D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The static exact-design theorem is expressed as a law of two Boolean CUT readouts. -/

import D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

/- Library-search audit trail (2026-09-04): repository searches found the canonical
   `jointReadout` and frozen `static_exact_design`; both are imported and reused.
   Pinned Mathlib supplies finite instances for `Fin 3`, `Bool`, and `Fin 0`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- The two CUT roles in the static experiment-design statement. -/
abbrev StaticReadout := Fin 2

/-- Typed signature of the two Boolean experiment responses. -/
abbrev staticSignature : PrimitiveSignature (Fin 3) where
  Index := StaticReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by
    intro i
    cases i <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- The exact proposition proved by the frozen source theorem. -/
def StaticExactDesignStatement : Prop :=
  let changeX : Fin 3 -> Bool := fun model => decide (model = 1)
  let changeY : Fin 3 -> Bool := fun model => decide (model = 2)
  (forall experiment : Bool,
      Not (Function.Injective
        (fun model => if experiment then changeY model else changeX model))) /\
    Function.Injective
      (jointReadout (fun experiment : Bool =>
        if experiment then changeY else changeX)) /\
    forall selected : Finset Bool,
      Function.Injective
          (jointReadout
            (fun experiment : {candidate // candidate ∈ selected} =>
              if experiment.1 then changeY else changeX)) ->
        selected = {false, true}

/-- The source theorem rewritten over the two realization readouts. -/
def staticExactExperimentArena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Fin 3)
  signature := staticSignature
  Law := fun r =>
    (forall experiment : Bool,
        Not (Function.Injective (fun model =>
          if experiment then r.readout (1 : StaticReadout) model
            else r.readout (0 : StaticReadout) model))) /\
      Function.Injective
        (jointReadout (fun experiment : Bool =>
          if experiment then r.readout (1 : StaticReadout)
            else r.readout (0 : StaticReadout))) /\
      forall selected : Finset Bool,
        Function.Injective
            (jointReadout
              (fun experiment : {candidate // candidate ∈ selected} =>
                if experiment.1 then r.readout (1 : StaticReadout)
                  else r.readout (0 : StaticReadout))) ->
          selected = {false, true}

/-- The static exact-experiment arena has at least two source models. -/
theorem staticExactExperimentArena_nondegenerate :
    staticExactExperimentArena.toArena.Nondegenerate := by decide

end D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
