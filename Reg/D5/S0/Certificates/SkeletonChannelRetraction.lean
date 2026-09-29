import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
import Reg.Support.PointwiseDisequalityRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S0.Certificates.SkeletonChannelRetraction
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      statementIdentity := "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      statementIdentity := "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two,
      statementIdentity := "sha256:5d44afb033ddb3092bb7a2e8025826dbb3617a6a8c332bfe7ea171362b77ead2",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.digitArena, theoremName := `D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero,
      statementIdentity := "sha256:7af706b36940ff69c2a70352c0a715b51cd4cac8c3d1ee9c762770d82221d2b4",
      registrationModuleName := `Reg.D5.S0.Certificates.SkeletonChannelRetraction }]
  companionPrefix := some `Reg.D5.S0.Certificates.SkeletonChannelRetraction }

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

register_information_theorem _root_.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two in digitArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.recurrentReadout d) (fun _ => digitTwo))
  primitives recurrentRealization.toPrimitiveBundle realization recurrent_bridge
  variation recurrent_lawSensitive sensitivity digit_slotSensitive
  escape from (Fin 4) escape continues (recurrentResidual)
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

register_information_theorem _root_.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero in digitArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseNeRealization
    (Fin 4) (Fin 4) (instDecidableEqFin 4)
    (fun d => D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations.transientReadout d) (fun _ => digitZero))
  primitives transientRealization.toPrimitiveBundle realization transient_bridge
  variation transient_lawSensitive sensitivity digit_slotSensitive
  escape from (Fin 4) escape continues (transientResidual)
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
example : _root_.Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.recurrentRetract_ne_two.__information_unit.Statement =
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
example : _root_.Reg.D5.S0.Certificates.SkeletonChannelRetraction.D5.S0.Certificates.SkeletonChannelRetraction.transientRetract_ne_zero.__information_unit.Statement =
    (∀ d : Fin 4, transientRetract d ≠ 0) := rfl
end

end Reg.D5.S0.Certificates.SkeletonChannelRetraction
