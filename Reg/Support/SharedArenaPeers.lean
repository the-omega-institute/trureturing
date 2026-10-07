import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
noncomputable def _root_.Reg.Support.SharedArenaPeers.enrollment_1 : LeanInformationAudit.Contract.TemplateEnrollment.{2, max 0 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.interventionFiniteRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.interventionFiniteRealization, version := 1, constructors := #[{ name := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM, type := (D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM) }],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.SharedArenaPeers.enrollment_1.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.interventionFiniteRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.interventionFiniteRealization, part := .value, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation, declaration := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM, part := .type, path := [], levels := [] }], facts := [] } }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
noncomputable def _root_.Reg.Support.SharedArenaPeers.enrollment_2 : LeanInformationAudit.Contract.TemplateEnrollment.{2, max (max 0 0) 0} (@_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization, version := 1, constructors := #[{ name := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection, type := (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection) }, { name := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM, type := (D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) }],
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxRecDepth, value := .nat 100000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  bodyFact := `Reg.Support.SharedArenaPeers.enrollment_2.bodyFact,
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates, declaration := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization, part := .value, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation, declaration := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.CausalDirection, part := .type, path := [], levels := [] },
    { owner := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation, declaration := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM, part := .type, path := [], levels := [] }], facts := [] } }

end

noncomputable def Reg.Support.SharedArenaPeers.enrollment_2.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"SharedArenaPeers\",\"enrollment_2\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SharedArenaFiniteTemplates\",\"observationFiniteRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.Support.SharedArenaPeers.enrollment_1.bodyFact : LeanInformationAudit.Contract.NodeFact :=
  compiled_exact% "{\"declaration\":[\"Reg\",\"Support\",\"SharedArenaPeers\",\"enrollment_1\"],\"part\":\"type\",\"path\":[\"argument\"],\"levels\":[]}" "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"InformationEscape\",\"SharedArenaFiniteTemplates\",\"interventionFiniteRealization\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"
