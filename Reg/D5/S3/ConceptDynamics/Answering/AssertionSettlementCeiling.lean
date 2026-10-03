import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import Reg.Support.IffRegistrations



namespace Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling

noncomputable def _root_.Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena (∀ (c : D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.Claim), Iff (@Eq.{1} Bool (D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.permits D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.Outcome.open c) Bool.true) (@Eq.{1} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.Claim c D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.Claim.unsettled)) D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) (type_of% (openCodeArena)) (type_of% (openCodeArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    (Fin 5) (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))) (type_of% (open_lawSensitive)) (type_of% (open_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(openCodeArena)⟩,
  objectArena := ⟨(openCodeArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (openCodeArena) (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization) (openRealization.toPrimitiveBundle) ⟨(open_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    (Fin 5) (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := some ⟨(open_lawSensitive)⟩,
  sensitivity := some ⟨(open_slotSensitive)⟩,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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
