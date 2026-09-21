import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import Reg.Support.IffRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled,
      statementIdentity := "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled,
      statementIdentity := "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling }

namespace Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

register_information_theorem _root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled in openCodeArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    (Fin 5) (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  primitives openRealization.toPrimitiveBundle realization open_bridge
  variation open_lawSensitive sensitivity open_slotSensitive
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
example : _root_.Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled.__information_unit.Statement =
    (∀ c : Claim, permits .open c = true ↔ c = .unsettled) := rfl
end

end Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
