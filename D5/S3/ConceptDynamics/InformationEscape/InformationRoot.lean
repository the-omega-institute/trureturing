/- GID: D5/S3/ConceptDynamics/InformationEscape/InformationRoot
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/InformationRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One elaboration registers and seals ten frozen theorems and one system theorem. -/

import LeanInformationAudit.SealCommand
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit

/- Library-search audit trail (2026-09-04):
   * Exact repository searches found all ten frozen source theorems, their
     eleven arena/realization exports, and the corresponding
     `LegacyPrimitiveRealization` certificates imported below.
   * `LeanInformationAudit.Syntax` and `SealCommand` are the unique command
     owners; the root uses their registration and terminal sealing commands
     directly rather than reproducing registry or proof-construction logic.
   * No existing information root or production registration of these frozen
     theorems was found under `D5` or `Blueprint`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.InformationRoot

open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscape.SystemUnit

attribute [local instance]
  contextDecidableEq
  modelDecidableEq

local instance systemArenaStateDecidableEq : DecidableEq arena.toArena.State :=
  arena.toArena.stateDecidableEq

/-! The specification's suggested `D5/InformationRoot.lean` location is not a
canonical GID: D5 declarations require three or four path components after D5.
This root therefore lives under the registered `ConceptDynamics` S3 domain.

Each of the ten frozen legacy theorems, and the additional system theorem, is
deliberately alone in its own arena. Consequently every leave-one-out catalog
is empty and each reported unique capture is the unit's entire escape set.
This satisfies the positive-capture seal while making no claim about redundancy
between units that share an arena. All registrations and the seal elaborate in
this single module compilation. -/

register_information_theorem
  agenda_power
  in agendaPowerArena
  primitives agendaPowerRealization.toPrimitiveBundle
  realization agenda_power_realization

register_information_theorem
  two_step_adaptive_residue_identification
  in residueArena
  primitives residueRealization.toPrimitiveBundle
  realization two_step_adaptive_residue_identification_realization

register_information_theorem
  spectrum_atom_index_bijective
  in spectrumArena
  primitives spectrumRealization.toPrimitiveBundle
  realization spectrum_atom_index_bijective_realization

register_information_theorem
  context_parameters_can_select_distinct_fixed_points
  in contextArena
  primitives contextRealization.toPrimitiveBundle
  realization context_parameters_can_select_distinct_fixed_points_realization

register_information_theorem
  intervention_strictly_weaker_than_counterfactual
  in interventionArena
  primitives interventionRealization.toPrimitiveBundle
  realization intervention_strictly_weaker_than_counterfactual_realization

register_information_theorem
  observation_strictly_weaker_than_intervention
  in observationInterventionArena
  primitives observationInterventionRealization.toPrimitiveBundle
  realization observation_strictly_weaker_than_intervention_realization

register_information_theorem
  static_exact_design
  in staticExactExperimentArena
  primitives staticExactExperimentRealization.toPrimitiveBundle
  realization static_exact_design_realization

register_information_theorem
  commutativity_hypothesis_is_necessary
  in commutingCompletionArena
  primitives commutingCompletionRealization.toPrimitiveBundle
  realization commutativity_hypothesis_is_necessary_realization

register_information_theorem
  compatible_local_laws_can_lack_global_state
  in localLawGluingArena
  primitives localLawGluingRealization.toPrimitiveBundle
  realization compatible_local_laws_can_lack_global_state_realization

register_information_theorem
  end_state_omits_preempting_cause
  in endStateOmitsPreemptingCauseArena
  primitives endStateOmitsPreemptingCauseRealization.toPrimitiveBundle
  realization end_state_omits_preempting_cause_realization

register_information_theorem
  engine_census_self_application
  in arena
  primitives systemRealization.toPrimitiveBundle
  realization system_self_application_realization

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The seal decides eleven finite catalogs and kernel-checks every generated proof.
#seal_information_theory

end D5.S3.ConceptDynamics.InformationEscape.InformationRoot
