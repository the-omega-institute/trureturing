/- L0 原型 -/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog
import Reg.ContractPrototype.Templates.Iff

namespace Reg.ContractPrototype.Readout
open LeanInformationAudit.Contract
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates

def declaration : Registration D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
    PrimitiveLawArena PrimitiveLawArena
    (PrimitiveRealization openCodeArena.signature)
    (openCodeArena.Law openRealization ∧ ¬ openCodeArena.Law
      (iffRealization (fun _ : Fin 5 => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity openCodeArena) Unit Unit Unit where
  targetName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  catalog := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
  localNames := true
  realization := .legacy openCodeArena openRealization (openRealization.toPrimitiveBundle) ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge, open_bridge⟩
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive, open_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_slotSensitive, open_slotSensitive⟩
  escapeFrom := none
  sourceSelection := none
  continuation := .absent
  familyRecord := none
  options := {}

def expectation : ExpectedOccurrence where
  statement := _
  proof := D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
  statementIdentity := some "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e"
  registrationModuleName := `Reg.ContractPrototype.Readout

def rootDeclaration : RootCatalog where
  data := {
    rootId := `Reg.ContractPrototype.Readout
    expected := #[expectation]
    source := #[expectation]
    baseline := #[]
    companionPrefix := some `Reg.ContractPrototype.Readout }

end Reg.ContractPrototype.Readout
