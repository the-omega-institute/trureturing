import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import Reg.Support.PointwiseEqualityRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction,
      statementIdentity := "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc",
      registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction,
      statementIdentity := "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc",
      registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }]
  companionPrefix := some `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }

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

register_information_theorem _root_.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction in recenterArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 2) (instDecidableEqFin 2)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d) (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterReadout d))
  primitives recenterRealization.toPrimitiveBundle realization recenter_bridge
  variation recenter_lawSensitive sensitivity recenter_slotSensitive
  escape from (Fin 3) escape continues (recenterResidual)
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
example : _root_.Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction.__information_unit.Statement =
    (∀ d : Fin 3, recenter d (direction d) = (0, 0)) := rfl
end

end Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
