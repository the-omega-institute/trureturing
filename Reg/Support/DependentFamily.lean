import LeanInformationAuditInterface.Contract.NodeFactsCore
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable def _root_.Reg.Support.DependentFamily.enrollment_1.{t, s, r, o, a} : LeanInformationAudit.Contract.TemplateEnrollment.{max (max (max (max (a + 2) (o + 2)) (r + 2)) (s + 2)) (t + 2), 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{t, s, r, o, a}) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

namespace Reg.Support.DependentFamily
open LeanInformationAudit.Contract

noncomputable def bodyFact.{t,s,r,o,a} : NodeFact := .equal
  (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{t,s,r,o,a})
  (fun S readout anchor => ⟨readout, anchor⟩)
  { owner := `Reg.Support.DependentFamily, declaration := `Reg.Support.DependentFamily.enrollment_1,
    part := .type, path := [.argument],
    levels := [.param `t, .param `s, .param `r, .param `o, .param `a] }
  { owner := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily,
    declaration := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize,
    part := .value, path := [],
    levels := [.param `t, .param `s, .param `r, .param `o, .param `a] }
  rfl

end Reg.Support.DependentFamily
