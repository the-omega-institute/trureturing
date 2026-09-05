import LeanInformationAudit.SnapshotTypes

namespace LeanInformationAudit

/-- Immutable AC-019 expectation baseline, copied from the eleven occurrence rows
of source snapshot 6a48d8d7061636c6b33ba77fb5954d7dc9da8a7d. SnapshotEnumerator
never writes this historical baseline; new contributors belong to FixedSnapshot. -/
def frozenInformationRootBaseline : Array SnapshotOccurrence :=
  #[{ objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena,
                     theoremName := `D5.S3.ConceptDynamics.InformationEscape.SystemUnit.engine_census_self_application,
                     statementIdentity := "sha256:a3a2c21de13a5366dbb0d8ab39bc747e95b22c7cbeecb7ef39d86092b4c70ab0",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena,
                     theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
                     statementIdentity := "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena,
                     theoremName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause,
                     statementIdentity := "sha256:b93e6bd918cabb38e32a21f11542a80c47dcc6ba73bdeac72336a5c75648c24c",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.agendaPowerArena,
                     theoremName := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power,
                     statementIdentity := "sha256:384a1edc32c16ec0b4045c373ce00d995b3fa571bb9cbf36960355b33a93cc00",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena,
                     theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
                     statementIdentity := "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.spectrumArena,
                     theoremName := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.spectrum_atom_index_bijective,
                     statementIdentity := "sha256:970d0c4dbc3081113fb682ad75b2e6ee7f11e8330ded5624aa79599b799b76b3",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.contextArena,
                     theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points,
                     statementIdentity := "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.interventionArena,
                     theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
                     statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena,
                     theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
                     statementIdentity := "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena,
                     theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
                     statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot },
                   { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena,
                     theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
                     statementIdentity := "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a",
                     registrationModuleName := `D5.S3.ConceptDynamics.InformationEscape.InformationRoot }]

end LeanInformationAudit

