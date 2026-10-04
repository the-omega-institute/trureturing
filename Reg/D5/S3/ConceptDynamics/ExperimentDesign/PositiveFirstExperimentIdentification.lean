import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
import Reg.Support.GuardedEqualityRegistrations



namespace Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
open GuardedEqualityRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model) (type_of% (positiveFirstArena)) (type_of% (positiveFirstArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun model => positiveFirstReadout model) (fun model => model) (fun _ => modelXYCode))) (type_of% (positiveFirst_lawSensitive)) (type_of% (positiveFirst_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirst_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(positiveFirstArena)⟩,
  objectArena := ⟨(positiveFirstArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (positiveFirstArena) (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstRealization) (positiveFirstRealization.toPrimitiveBundle) ⟨(positiveFirst_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun model => positiveFirstReadout model) (fun model => model) (fun _ => modelXYCode)),
  variation := some ⟨(positiveFirst_lawSensitive)⟩,
  sensitivity := some ⟨(positiveFirst_slotSensitive)⟩,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
open GuardedEqualityRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirst_bridge.toTheoremUnit _root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model).Statement =
    (∀ (model : Fin 3) (_hpositive : E_X model = true), model = M_XY) := rfl
end

end Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
