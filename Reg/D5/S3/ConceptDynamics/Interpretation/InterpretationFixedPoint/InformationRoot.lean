import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.LegacyContextReplacement
import D5.S3.ConceptDynamics.InformationEscape.ExactRate
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.HierarchyLaws
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.LayeredCapture
import D5.S3.ConceptDynamics.InformationEscapeHierarchy.RefinementMatrix
import D5.S3.ConceptDynamics.RegistrationWitnesses




namespace Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open Reg.Support.LegacyContextReplacement
open LeanInformationAudit

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.context_parameters_can_select_distinct_fixed_points) (type_of% (domainArena)) (type_of% (objectArena)) (type_of% (cutRealization (fun x : ContextData => Reg.Support.LegacyContextCausalCodes.contextCode x))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.baselineContext)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interpretation") "InterpretationFixedPoint") "context_parameters_can_select_distinct_fixed_points") "Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot/Reg.Support.LegacyContextReplacement.objectArena/Reg.Support.LegacyContextReplacement.objectArena") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Interpretation") "InterpretationFixedPoint") "context_parameters_can_select_distinct_fixed_points") "Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot/Reg.Support.LegacyContextReplacement.objectArena/Reg.Support.LegacyContextReplacement.objectArena") "__primitive_realization"),
  realizationSource := some `Reg.Support.LegacyContextReplacement.bridge,
  generated := false,
  arena := ⟨(domainArena)⟩,
  objectArena := ⟨(objectArena)⟩,
  catalog := `Reg.Support.LegacyContextReplacement.objectArena,
  localNames := false,
  realization := .legacy (Reg.Support.LegacyContextReplacement.lawArena) (Reg.Support.LegacyContextReplacement.actual) (actual.toPrimitiveBundle) ⟨(bridge)⟩,
  readout := some (cutRealization (fun x : ContextData => Reg.Support.LegacyContextCausalCodes.contextCode x)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (_root_.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.baselineContext),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint.InformationRoot
