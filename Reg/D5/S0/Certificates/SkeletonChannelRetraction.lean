import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
import Reg.Support.PointwiseDisequalityRegistrations



namespace Reg.D5.S0.Certificates.SkeletonChannelRetraction

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentReadout d) (fun _ => digitTwo))) (type_of% (Fin 4)) (type_of% (recurrentResidual)) := {
  unitName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrent_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(digitArena)⟩,
  objectArena := .law ⟨(digitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (digitArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentRealization) (recurrentRealization.toPrimitiveBundle) ⟨(recurrent_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (recurrent_bridge) (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((recurrentRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentReadout d) (fun _ => digitTwo)),
  variation := .evidence ⟨(recurrent_lawSensitive)⟩ (by first | exact (recurrent_lawSensitive) | exact ⟨_, _, (recurrent_lawSensitive)⟩),
  sensitivity := .evidence ⟨(digit_slotSensitive)⟩ (by exact (digit_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := some (Fin 4),
  sourceSelection := none,
  continuation := .evidence ⟨(recurrentResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Certificates.SkeletonChannelRetraction, declaration := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalArenaFact, `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalObjectArenaFact] },
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction



noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientReadout d) (fun _ => digitZero))) (type_of% (Fin 4)) (type_of% (transientResidual)) := {
  unitName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transient_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(digitArena)⟩,
  objectArena := .law ⟨(digitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (digitArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientRealization) (transientRealization.toPrimitiveBundle) ⟨(transient_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (transient_bridge) (@_root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((transientRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientReadout d) (fun _ => digitZero)),
  variation := .evidence ⟨(transient_lawSensitive)⟩ (by first | exact (transient_lawSensitive) | exact ⟨_, _, (transient_lawSensitive)⟩),
  sensitivity := .evidence ⟨(digit_slotSensitive)⟩ (by exact (digit_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := some (Fin 4),
  sourceSelection := none,
  continuation := .evidence ⟨(transientResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Certificates.SkeletonChannelRetraction, declaration := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalArenaFact, `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalObjectArenaFact] },
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrent_bridge.toTheoremUnit _root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two).Statement =
    (∀ d : Fin 4, recurrentRetract d ≠ 2) := rfl
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Certificates.SkeletonChannelRetraction
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transient_bridge.toTheoremUnit _root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero).Statement =
    (∀ d : Fin 4, transientRetract d ≠ 0) := rfl
end

end Reg.D5.S0.Certificates.SkeletonChannelRetraction


noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena
noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena
noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena
noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena
noncomputable def Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Certificates\",\"SkeletonChannelRetraction\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Certificates.SkeletonChannelRetraction, declaration := `Reg.D5.S0.Certificates.SkeletonChannelRetraction.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
