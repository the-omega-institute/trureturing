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




namespace Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.Support.LegacyFiniteTransport
open _root_.Reg.Support.LegacyAgenda

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power) (type_of% (arena)) (type_of% (arena)) (type_of% (agendaRealization (fun s => winnerCode s) (fun s => valid s))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.Agenda)) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot.D5.S3.ConceptDynamics.Aggregation.AgendaPower.agenda_power.__information_unit,
  realizationName := `Reg.Support.LegacyAgenda.bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} Reg.Support.LegacyAgenda.arena) (Reg.Support.LegacyAgenda.actual) (actual.toPrimitiveBundle) ⟨(bridge)⟩,
  readout := some (agendaRealization (fun s => winnerCode s) (fun s => valid s)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Aggregation.AgendaPower.Agenda),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.ConceptDynamics.Aggregation.AgendaPower.InformationRoot
