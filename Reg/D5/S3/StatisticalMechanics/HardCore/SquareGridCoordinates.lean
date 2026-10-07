import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import Reg.Support.PointwiseEqualityRegistrations



namespace Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open _root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 2) (instDecidableEqFin 2)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d) (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d))) (type_of% (Fin 3)) (type_of% (recenterResidual)) := {
  unitName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenter_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(recenterArena)⟩,
  objectArena := .law ⟨(recenterArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (recenterArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization) (recenterRealization.toPrimitiveBundle) ⟨(recenter_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (recenter_bridge) (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((recenterRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 2) (instDecidableEqFin 2)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d) (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d)),
  variation := .evidence ⟨(recenter_lawSensitive)⟩ (by first | exact (recenter_lawSensitive) | exact ⟨_, _, (recenter_lawSensitive)⟩),
  sensitivity := .evidence ⟨(recenter_slotSensitive)⟩ (by exact (recenter_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := some (Fin 3),
  sourceSelection := none,
  continuation := .evidence ⟨(recenterResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalArenaFact, `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalObjectArenaFact] },
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open _root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenter_bridge.toTheoremUnit _root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction).Statement =
    (∀ d : Fin 3, recenter d (direction d) = (0, 0)) := rfl
end

end Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates


noncomputable def Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena
noncomputable def Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"HardCore\",\"SquareGridCoordinates\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"HardCore\",\"SquareGridCoordinates\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena
noncomputable def Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"HardCore\",\"SquareGridCoordinates\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"StatisticalMechanics\",\"HardCore\",\"SquareGridCoordinates\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates, declaration := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
