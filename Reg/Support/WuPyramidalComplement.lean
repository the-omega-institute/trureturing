import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.Arith.WuPyramidalComplement

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.Arith.WuPyramidalComplement
attribute [local instance] _root_.D5.S3.Arith.WuPyramidalComplement.instDecidable_d5
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit
noncomputable def _root_.Reg.Support.WuPyramidalComplement.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{1, 0} (@_root_.D5.S3.Arith.WuPyramidalComplement.branchRealization) := {
  name := `D5.S3.Arith.WuPyramidalComplement.branchRealization, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end
