import LeanInformationAuditInterface.RootContract
import Reg.Support.FixedSnapshot
import Reg.Support.FrozenBaseline

namespace Reg.Support.TemplateShadowContract
open Lean LeanInformationAudit

def rootId : Name := `Reg.Catalogs.TemplateShadow

-- TemplateShadow supplies the same ten mathematical occurrences as the
-- independent baseline, excluding SystemUnit. Only the producer differs.
-- Statement identities retain theoremStatementIdentity's toString-type hash.
def occurrences : Array SnapshotOccurrence :=
  #[
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena,
                     theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
                     statementIdentity := "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena,
                     theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause,
                     statementIdentity := "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena,
                     theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
                     statementIdentity := "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena,
                     theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
                     statementIdentity := "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena,
                     theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective,
                     statementIdentity := "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena,
                     theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points,
                     statementIdentity := "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena,
                     theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
                     statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena,
                     theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
                     statementIdentity := "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena,
                     theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
                     statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow },
  { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena,
                     theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
                     statementIdentity := "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a",
                     registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow }]

def contract : RootCatalogContract := {
  rootId
  expected := occurrences
  source := occurrences
  baseline := occurrences
  companionPrefix := some rootId }

-- Independently translated from the existing D5 seal: only catalog, verdict,
-- unit and certificate names change to this root's generated names.
def expectedSealDigest : String :=
  "ef013c5f573c8bfe35cdc82d8422fb8674b69d82925938ad809316a289bf146f"

end Reg.Support.TemplateShadowContract
