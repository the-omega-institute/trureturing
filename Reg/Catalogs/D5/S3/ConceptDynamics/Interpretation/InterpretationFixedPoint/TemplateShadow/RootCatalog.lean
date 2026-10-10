import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses
import Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow
import Reg.Support.LegacyContextReplacement

namespace Reg.Catalogs.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow.RootCatalog
open LeanInformationAudit

def rootCatalog : Contract.RootCatalog := { data := {
  rootId := `Reg.Catalogs.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow.RootCatalog,
  expected := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow }],
  source := #[{ statement := (_), proof := (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points), theoremName := `D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points, objectArenaName := `Reg.Support.LegacyContextReplacement.objectArena, statementIdentity := some "sha256:778398ffe72817b135e29453ae9a3b796de14383670686abbf230840cb7ee515", registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow }],
  baseline := #[],
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow } }

end Reg.Catalogs.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.TemplateShadow.RootCatalog
