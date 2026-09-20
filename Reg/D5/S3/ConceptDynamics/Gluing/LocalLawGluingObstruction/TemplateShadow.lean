import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena, theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
      statementIdentity := "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction.localLawGluingArena, theoremName := `D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state,
      statementIdentity := "sha256:95b576248df546ed3529c83c5c171a1ab2f6cff8fd9f78d7db83204dd4ecfb56",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open InformationEscapeArenas.LocalLawGluingObstruction

register_information_theorem _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state in localLawGluingArena
  primitives gluingRealization.toPrimitiveBundle realization gluing_bridge
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open InformationEscapeArenas.LocalLawGluingObstruction
example : _root_.Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state.__information_unit.Statement =
    (InformationEscapeRealizations.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state_realization.toTheoremUnit
      compatible_local_laws_can_lack_global_state).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
