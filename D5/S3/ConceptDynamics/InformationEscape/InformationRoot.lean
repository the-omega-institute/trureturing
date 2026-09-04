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

attribute [local instance]
  _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextDecidableEq
  _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelDecidableEq

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
  _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.agendaPowerRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.agenda_power_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.residueRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.two_step_adaptive_residue_identification_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.spectrumRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations.spectrum_atom_index_bijective_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations.contextRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations.context_parameters_can_select_distinct_fixed_points_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations.interventionRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations.intervention_strictly_weaker_than_counterfactual_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention.observationInterventionRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention.observation_strictly_weaker_than_intervention_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign.staticExactExperimentRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign.static_exact_design_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutingCompletionRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange.commutativity_hypothesis_is_necessary_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction.localLawGluingRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause
  in _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization

register_information_theorem
  _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.bool_pair_fst_snd_catalog_irredundant
  in _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.boolPairFstSndArena
  primitives _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.boolPairFstSndRealization.toPrimitiveBundle
  realization _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit.bool_pair_fst_snd_catalog_irredundant_realization

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The seal decides eleven finite catalogs and kernel-checks every generated proof.
#seal_information_theory

end D5.S3.ConceptDynamics.InformationEscape.InformationRoot
