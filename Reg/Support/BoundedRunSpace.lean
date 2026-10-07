import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
open _root_.D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
noncomputable def _root_.Reg.Support.BoundedRunSpace.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{2, max 0 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization, version := 1, constructors := #[{ name := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom, type := (D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom) }],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.BoundedRunSpace.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization, part := .value, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope, declaration := `D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope.SpectrumAtom, part := .type, path := [], levels := [] }], facts := [] } }

end

noncomputable def Reg.Support.BoundedRunSpace.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"BoundedRunSpace\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"RegistrationTemplates\",\"cutRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
