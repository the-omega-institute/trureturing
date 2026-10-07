import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    (Fin 5) (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(openCodeArena)⟩,
  objectArena := .law ⟨(openCodeArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (openCodeArena) (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openRealization) (openRealization.toPrimitiveBundle) ⟨(open_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (open_bridge) (@_root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((openRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    (Fin 5) (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨(open_lawSensitive)⟩ (by first | exact (open_lawSensitive) | exact ⟨_, _, (open_lawSensitive)⟩),
  sensitivity := .evidence ⟨(open_slotSensitive)⟩ (by exact (open_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge.toTheoremUnit _root_.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled).Statement =
    (∀ c : Claim, permits .open c = true ↔ c = .unsettled) := rfl
end

end Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling


noncomputable def Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
noncomputable def Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Answering\",\"AssertionSettlementCeiling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Answering\",\"AssertionSettlementCeiling\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
noncomputable def Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Answering\",\"AssertionSettlementCeiling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Answering\",\"AssertionSettlementCeiling\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
