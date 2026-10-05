import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyGluing
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses




namespace Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.Support.LegacyFiniteTransport
open _root_.Reg.Support.LegacyGluing

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state) (type_of% (admitRealization (fun i s => readouts i s))) (type_of% (Bool × Bool × Bool)) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state.__information_unit,
  realizationName := `Reg.Support.LegacyGluing.bridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(arena)⟩,
  objectArena := .object ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} Reg.Support.LegacyGluing.arena) (Reg.Support.LegacyGluing.actual) (actual.toPrimitiveBundle) ⟨(bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (bridge) (@_root_.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((actual.toPrimitiveBundle)).Nonempty; decide),
  readout := some (admitRealization (fun i s => readouts i s)),
  variation := .evidence ⟨(variation)⟩ (by first | exact (variation) | exact ⟨_, _, (variation)⟩),
  sensitivity := .evidence ⟨(sensitivity)⟩ (by exact (sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (Bool × Bool × Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction.TemplateShadow
