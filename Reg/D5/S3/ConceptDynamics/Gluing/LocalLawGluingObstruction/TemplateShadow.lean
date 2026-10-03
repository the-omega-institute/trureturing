import Reg.Support.LegacyGluing
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
  expected := #[
    { objectArenaName := `Reg.Support.LegacyGluing.arena, theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
      statementIdentity := "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyGluing.arena, theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
      statementIdentity := "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow }


namespace Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.Support.LegacyFiniteTransport
open _root_.Reg.Support.LegacyGluing

register_information_theorem _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state in arena
  readout via (admitRealization (fun i s => readouts i s))
  primitives actual.toPrimitiveBundle
  realization bridge
  variation variation
  sensitivity sensitivity
  escape from (Bool × Bool × Bool) escape continues (open)

end Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
