import LeanInformationAudit.Census.Query
import Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow
import Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow
import Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow
import Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
import Reg.Support.TemplateShadowContract
import LeanInformationAudit.SealCommand

open Lean LeanInformationAudit

run_cmd RootCatalogs.declare Reg.Support.TemplateShadowContract.contract

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Seal the existing finite catalogs under the production seal limit.
#seal_information_theory


section
open LeanInformationAudit
open Lean Meta LeanInformationAudit in
run_meta do
  let env ← getEnv
  let index ← CensusQuery.indexScope env.header.mainModule
  let head ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  unless head.exitCode == 0 do throwError "cannot read checkout identity"
  let cases := #[
    (``D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena),
    (``D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena),
    (``D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena),
    (``D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena),
    (``D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena),
    (``D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena),
    (``D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena),
    (``D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena),
    (``D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena),
    (``D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
      ``D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena)]
  for (gold, arena) in cases do
    let key : StatementKey := ⟨gold, theoremStatementIdentity env gold⟩
    match ← CensusQuery.assess index head.stdout.trimAscii.toString key with
    | .certified (.finiteOccurrence payload) =>
        unless payload.canonicalArena == arena do throwError "unexpected canonical arena"
        logInfo m!"CENSUS_QUERY_FINITE_VALIDATED: {key.theoremName}; {key.statementId}; {repr payload}"
    | _ => throwError "finite occurrence was not certified: {gold}"
end

#print axioms D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena/D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena/D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena/D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena/D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena/D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena».__lowers_escape
#print axioms D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification.«Reg.Catalogs.TemplateShadow/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena/D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena».__lowers_escape
