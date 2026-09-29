import LeanInformationAudit.ReadoutProvenance
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit

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
open Lean LeanInformationAudit.RegistrationGates
run_cmd Elab.Command.liftCoreM do
  let root := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot
  let mut total : ProvenanceCounters := {}
  for (label, theoremName, realization) in [
      ("agenda_power", ``agenda_power, ``agenda_power_realization),
      ("two_step_adaptive_residue_identification", ``two_step_adaptive_residue_identification, ``two_step_adaptive_residue_identification_realization),
      ("spectrum_atom_index_bijective", ``spectrum_atom_index_bijective, ``spectrum_atom_index_bijective_realization),
      ("context_parameters_can_select_distinct_fixed_points", ``context_parameters_can_select_distinct_fixed_points, ``context_parameters_can_select_distinct_fixed_points_realization),
      ("intervention_strictly_weaker_than_counterfactual", ``intervention_strictly_weaker_than_counterfactual, ``intervention_strictly_weaker_than_counterfactual_realization),
      ("observation_strictly_weaker_than_intervention", ``observation_strictly_weaker_than_intervention, ``observation_strictly_weaker_than_intervention_realization),
      ("static_exact_design", ``static_exact_design, ``static_exact_design_realization),
      ("commutativity_hypothesis_is_necessary", ``commutativity_hypothesis_is_necessary, ``commutativity_hypothesis_is_necessary_realization),
      ("compatible_local_laws_can_lack_global_state", ``compatible_local_laws_can_lack_global_state, ``compatible_local_laws_can_lack_global_state_realization),
      ("end_state_omits_preempting_cause", ``end_state_omits_preempting_cause, ``end_state_omits_preempting_cause_realization),
      ("engine_census_self_application", ``engine_census_self_application, ``system_self_application_realization)] do
    let actual ← withOptions (·.set `trace.InformationProvenance.check true) <|
      provenanceErrorCurrent root `catalog theoremName realization
    let counts ← getProvenanceCounters
    total := { total with
      chargedVisits := total.chargedVisits + counts.chargedVisits,
      recheckedNodes := total.recheckedNodes + counts.recheckedNodes,
      canonicalizations := total.canonicalizations + counts.canonicalizations,
      traversalWork := total.traversalWork + counts.traversalWork }
    if actual.isNone then logInfo m!"[PASS] WitnessCorpus.{label}: {repr counts}"
    else logError m!"[FAIL] WitnessCorpus.{label}: {actual}"
  logInfo m!"WitnessCorpusTotal chargedVisits={total.chargedVisits} recheckedNodes={total.recheckedNodes} canonicalizations={total.canonicalizations} traversalWork={total.traversalWork}"
