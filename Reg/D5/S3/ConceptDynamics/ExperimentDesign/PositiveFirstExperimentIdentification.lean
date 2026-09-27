import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
import Reg.Support.GuardedEqualityRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model,
      statementIdentity := "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model,
      statementIdentity := "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification }

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

register_information_theorem _root_.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model in positiveFirstArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun model => positiveFirstReadout model) (fun model => model) (fun _ => modelXYCode))
  primitives positiveFirstRealization.toPrimitiveBundle realization positiveFirst_bridge
  variation positiveFirst_lawSensitive sensitivity positiveFirst_slotSensitive
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
example : _root_.Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model.__information_unit.Statement =
    (∀ (model : Fin 3) (_hpositive : E_X model = true), model = M_XY) := rfl
end

end Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
