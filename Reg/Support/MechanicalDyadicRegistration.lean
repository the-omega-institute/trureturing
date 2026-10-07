import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

noncomputable def _root_.Reg.Support.MechanicalDyadicRegistration.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{2, 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.mechanicalReadoutRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.mechanicalReadoutRealization, version := 1, constructors := #[],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.MechanicalDyadicRegistration.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration, declaration := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.mechanicalReadoutRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration, declaration := `D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration.mechanicalReadoutRealization, part := .value, path := [], levels := [] }], facts := [] } }

noncomputable def Reg.Support.MechanicalDyadicRegistration.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"MechanicalDyadicRegistration\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"MechanicalDyadicRegistration\",\"mechanicalReadoutRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
