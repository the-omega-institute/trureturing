import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
import Reg.Support.HughesIterationDepthNoGapRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.HughesIterationDepthNoGap
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthNoGapArena, theoremName := `D5.S1.Words.HughesIterationDepthNoGap.result,
      statementIdentity := "sha256:230f0680b60411b8adb201199c15d936e8d5cec2ffbba2159b694747c9dc2f0a",
      registrationModuleName := `Reg.D5.S1.Words.HughesIterationDepthNoGap }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration.depthNoGapArena, theoremName := `D5.S1.Words.HughesIterationDepthNoGap.result,
      statementIdentity := "sha256:230f0680b60411b8adb201199c15d936e8d5cec2ffbba2159b694747c9dc2f0a",
      registrationModuleName := `Reg.D5.S1.Words.HughesIterationDepthNoGap }]
  companionPrefix := some `Reg.D5.S1.Words.HughesIterationDepthNoGap }

namespace Reg.D5.S1.Words.HughesIterationDepthNoGap

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.HughesIterationDepthNoGapRegistration
open _root_.D5.S1.Words.HughesIterationDepthNoGap
open LeanInformationAudit
open RegistrationTemplates

register_information_theorem _root_.D5.S1.Words.HughesIterationDepthNoGap.result in depthNoGapArena
  readout via (depthOriginTemplate (fun origin => origin))
  primitives depthOriginRealization.toPrimitiveBundle
  realization inline depthOriginRealization := by exact ⟨Iff.rfl⟩
  variation depth_law_variation sensitivity depth_slot_sensitivity
  escape from (closedSourceZero) escape continues (open)
end

end Reg.D5.S1.Words.HughesIterationDepthNoGap
