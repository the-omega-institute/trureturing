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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction) (type_of% (recenterArena)) (type_of% (recenterArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 2) (instDecidableEqFin 2)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d) (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d))) (type_of% (recenter_lawSensitive)) (type_of% (recenter_slotSensitive)) (type_of% (Fin 3)) (type_of% (recenterResidual)) (Unit) := {
  unitName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenter_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(recenterArena)⟩,
  objectArena := ⟨(recenterArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (recenterArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterRealization) (recenterRealization.toPrimitiveBundle) ⟨(recenter_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 2) (instDecidableEqFin 2)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d) (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d)),
  variation := some ⟨(recenter_lawSensitive)⟩,
  sensitivity := some ⟨(recenter_slotSensitive)⟩,
  escapeFrom := some (Fin 3),
  sourceSelection := none,
  continuation := .evidence ⟨(recenterResidual)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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
