/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog
import Reg.ContractPrototype.Templates.Intervention

namespace Reg.ContractPrototype.Occurrence
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq

def propositionOf {P : Prop} (_proof : P) : Prop := P

def declaration : Registration interventional_marginal_sufficient_but_counterfactual_joint_not
    PrimitiveLawArena D5.S3.ConceptDynamics.InformationEscape.Arena
    (PrimitiveRealization finiteInterventionLawArena.signature)
    (finiteInterventionLawArena.Law finiteInterventionRealization ∧
      ¬ finiteInterventionLawArena.Law
        (interventionFiniteRealization (fun _ => c0) (fun _ => c0)))
    (LeanInformationAudit.FiniteSlotSensitivity finiteInterventionLawArena)
    Type (propositionOf finiteIntervention_empty) Unit where
  targetName := `D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionLawArena,
    finiteInterventionLawArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena,
    finiteInterventionArena⟩
  catalog := `finiteProbe
  localNames := false
  realization := .legacy finiteInterventionLawArena finiteInterventionRealization (finiteInterventionRealization.toPrimitiveBundle) ⟨`D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteTarget_bridge,
    finiteTarget_bridge⟩
  readout := some (@interventionFiniteRealization DeterministicBoolSCM
    (fun M => icIntCode M) (fun M => icCFCode M))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteIntervention_law_sensitive,
    finiteIntervention_law_sensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteIntervention_slot_sensitive,
    finiteIntervention_slot_sensitive⟩
  escapeFrom := some DeterministicBoolSCM
  sourceSelection := none
  continuation := .evidence ⟨`D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteIntervention_empty,
    finiteIntervention_empty⟩
  familyRecord := none
  options := Lean.Options.set
    (Lean.Options.set
      (Lean.Options.setBool {} `backward.isDefEq.respectTransparency.types false)
      `maxHeartbeats (2000000 : Nat))
    `maxRecDepth (100000 : Nat)

def expectation : ExpectedOccurrence where
  statement := _
  proof := interventional_marginal_sufficient_but_counterfactual_joint_not
  theoremName := `D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not
  objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena
  statementIdentity := some "sha256:8b649e1191e8e2c40391ae6cd263fafc09d16bf7c6c684f60f8ff7430cc97052"
  registrationModuleName := `Reg.ContractPrototype.Occurrence

def rootDeclaration : RootCatalog where
  data := {
    rootId := `Reg.ContractPrototype.Occurrence
    expected := #[expectation]
    source := #[expectation]
    baseline := #[]
    companionPrefix := some `Reg.ContractPrototype.Occurrence }
end Reg.ContractPrototype.Occurrence
