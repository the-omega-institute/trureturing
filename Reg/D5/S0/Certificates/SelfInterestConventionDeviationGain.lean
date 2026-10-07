import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.NodeFactsCore
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import Reg.Support.IffRegistrations



namespace Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention))) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(dualArena)⟩,
  objectArena := .law ⟨(dualArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (dualArena) (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization) (dualRealization.toPrimitiveBundle) ⟨(dual_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (dual_bridge) (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((dualRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention)),
  variation := .evidence ⟨(dual_lawSensitive)⟩ (by first | exact (dual_lawSensitive) | exact ⟨_, _, (dual_lawSensitive)⟩),
  sensitivity := .evidence ⟨(dual_slotSensitive)⟩ (by exact (dual_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalArenaFact, `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalObjectArenaFact] },
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
open _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge.toTheoremUnit _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff).Statement =
    (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) := rfl
end

end Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain

namespace Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
open LeanInformationAudit.Contract
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations

noncomputable def lawStatement : Prop := dualArena.Law dualRealization

noncomputable def bridgeFact : NodeFact := .equivalent
  (type_of% @_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff)
  (dualArena.Law dualRealization)
  { owner := `D5.S0.Certificates.SelfInterestConventionDeviationGain,
    declaration := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff,
    part := .type, path := [] }
  { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain,
    declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.lawStatement,
    part := .value, path := [] }
  dual_bridge.equivalence

end Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain


noncomputable def Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
noncomputable def Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SelfInterestConventionDeviationGain\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SelfInterestConventionDeviationGain\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena
noncomputable def Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SelfInterestConventionDeviationGain\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SelfInterestConventionDeviationGain\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, declaration := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
