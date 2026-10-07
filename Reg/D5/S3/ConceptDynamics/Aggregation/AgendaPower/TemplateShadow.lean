import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyAgenda
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses




namespace Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.Support.LegacyFiniteTransport
open _root_.Reg.Support.LegacyAgenda

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) (type_of% (agendaRealization (fun s => winnerCode s) (fun s => valid s))) (type_of% (_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.Agenda)) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power.__information_unit,
  realizationName := `Reg.Support.LegacyAgenda.bridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(arena)⟩,
  objectArena := .object ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} Reg.Support.LegacyAgenda.arena) (Reg.Support.LegacyAgenda.actual) (actual.toPrimitiveBundle) ⟨(bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (bridge) (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((actual.toPrimitiveBundle)).Nonempty; decide),
  readout := some (agendaRealization (fun s => winnerCode s) (fun s => valid s)),
  variation := .evidence ⟨(variation)⟩ (by first | exact (variation) | exact ⟨_, _, (variation)⟩),
  sensitivity := .evidence ⟨(sensitivity)⟩ (by exact (sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.Agenda),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Aggregation.AgendaPower, declaration := `D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow


noncomputable def Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  Reg.Support.LegacyAgenda.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Aggregation\",\"AgendaPower\",\"TemplateShadow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Aggregation\",\"AgendaPower\",\"TemplateShadow\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  Reg.Support.LegacyAgenda.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Aggregation\",\"AgendaPower\",\"TemplateShadow\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Aggregation\",\"AgendaPower\",\"TemplateShadow\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow, declaration := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.TemplateShadow.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
