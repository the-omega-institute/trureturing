import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
import Reg.Support.PointwiseOrderRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Powers.GoldenDesubstitution
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_pos,
      statementIdentity := "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_le_two,
      statementIdentity := "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_pos,
      statementIdentity := "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_le_two,
      statementIdentity := "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }]
  companionPrefix := some `Reg.D5.S1.Words.Powers.GoldenDesubstitution }

namespace Reg.D5.S1.Words.Powers.GoldenDesubstitution

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord

register_information_theorem _root_.D5.S1.Words.Powers.substLength_pos in strictArena
  object_arena objectArena catalog substitutionBounds
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun _ => lengthZero) (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b))
  primitives positiveRealization.toPrimitiveBundle realization positive_bridge
  variation positive_lawSensitive sensitivity strict_slotSensitive
  escape from (Bool) escape continues (positive_empty)
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord

register_information_theorem _root_.D5.S1.Words.Powers.substLength_le_two in weakArena
  object_arena objectArena catalog substitutionBounds
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b) (fun _ => lengthTwo))
  primitives upperRealization.toPrimitiveBundle realization upper_bridge
  variation upper_lawSensitive sensitivity weak_slotSensitive
  escape from (Bool) escape continues (upper_empty)
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord
example : substLength_pos.«Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__information_unit.Statement =
    (∀ b : Bool, 0 < (subst b).length) := rfl
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord
example : substLength_le_two.«Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__information_unit.Statement =
    (∀ b : Bool, (subst b).length ≤ 2) := rfl
end

end Reg.D5.S1.Words.Powers.GoldenDesubstitution
