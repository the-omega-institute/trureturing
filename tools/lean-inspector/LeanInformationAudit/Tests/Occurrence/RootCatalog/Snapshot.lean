import LeanInformationAudit.Tests.Occurrence.JointImport.Shared
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

open Lean Lean.Elab.Command LeanInformationAudit

-- Fully qualified theorem identities are the fixture inputs.
set_option linter.style.longLine false

namespace LeanInformationAudit.Tests.Occurrence.RootCatalog

-- Test-owned suppliers. The causal premises and arenas are pure D5 content;
-- no production registration root contributes any fixture rows.
def baselineRoot : Name := `LeanInformationAudit.Tests.Occurrence.RootCatalog.Baseline
def causalContributor : Name := `LeanInformationAudit.Tests.Occurrence.RootCatalog.Contributor
def designatedRoot : Name := `LeanInformationAudit.Tests.Occurrence.RootCatalog.Designated

-- Capture theorem identities before registration, in this supplier's compilation.
-- Consumers import the resulting values; they never reconstruct expected rows
-- from their registry or from their own environment's theorem declarations.
run_cmd do
  for (name, theoremName) in #[
      (`baselineIdentity, `LeanInformationAudit.Tests.Occurrence.JointImport.shared),
      (`observationIdentity,
        `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention),
      (`interventionIdentity,
        `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual)] do
    let value := Syntax.mkStrLit (theoremStatementIdentity (← getEnv) theoremName)
    elabCommand (← `(command| def $(mkIdent name) : String := $value))

def baselineRows : Array SnapshotOccurrence := #[{
  objectArenaName := `LeanInformationAudit.Tests.Occurrence.JointImport.arena
  theoremName := `LeanInformationAudit.Tests.Occurrence.JointImport.shared
  statementIdentity := baselineIdentity
  registrationModuleName := baselineRoot }]

def causalRows : Array SnapshotOccurrence := #[{
  objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena
  theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention
  statementIdentity := observationIdentity
  registrationModuleName := causalContributor }, {
  objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena
  theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
  statementIdentity := interventionIdentity
  registrationModuleName := causalContributor }]

def sourceRows : Array SnapshotOccurrence := baselineRows ++ causalRows

def baselineContract : RootCatalogContract := {
  rootId := baselineRoot, expected := baselineRows, source := sourceRows
  baseline := baselineRows, companionPrefix := some baselineRoot }

def designatedContract : RootCatalogContract := {
  rootId := designatedRoot, expected := sourceRows, source := sourceRows
  baseline := baselineRows, companionPrefix := some designatedRoot }

end LeanInformationAudit.Tests.Occurrence.RootCatalog
