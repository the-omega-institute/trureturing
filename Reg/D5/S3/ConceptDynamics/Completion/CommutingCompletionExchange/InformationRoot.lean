import LeanInformationAudit.Syntax
import LeanInformationAudit.SealCommand
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
      statementIdentity := "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange.commutingCompletionArena, theoremName := `D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary,
      statementIdentity := "sha256:1aed443dafdf76d41d4cca3a5a8bbf76e5a0f33e4a90453061b57fc3f432fb0a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot }

namespace Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower
open _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open _root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscape.SystemUnit
attribute [local instance]
  contextDecidableEq
  modelDecidableEq
local instance systemArenaStateDecidableEq : DecidableEq arena.toArena.State :=
  arena.toArena.stateDecidableEq

register_information_theorem _root_.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.commutativity_hypothesis_is_necessary
  in commutingCompletionArena
  primitives commutingCompletionRealization.toPrimitiveBundle
  realization commutativity_hypothesis_is_necessary_realization
end

end Reg.D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange.InformationRoot
