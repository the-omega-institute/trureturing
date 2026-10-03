import ContractPrototypeFixtures.ValidatedPartialOld
import Reg.Support.BoundedRunSpace
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion

open Lean LeanInformationAudit
run_cmd do
  let env ← getEnv
  let row : SnapshotOccurrence := {
    objectArenaName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena
    theoremName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary
    capturedStatement := captureStatement env
      `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary
    registrationModuleName := `Reg.ContractPrototype.Controls.ValidatedPartial }
  RootCatalogs.declare {
    rootId := `Reg.ContractPrototype.Controls.ValidatedPartial
    expected := #[row], source := #[row]
    companionPrefix := some `Reg.ContractPrototype.Controls.ValidatedPartial }

namespace Reg.ContractPrototype.Controls.ValidatedPartial
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
open D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
noncomputable section
register_information_theorem bounded_run_union_boundary in bitArena
  readout via (@cutRealization Bool Bool instDecidableEqBool Reg.ContractPrototype.Inputs.ValidatedPartialOld.route)
  primitives (@cutRealization Bool Bool instDecidableEqBool Reg.ContractPrototype.Inputs.ValidatedPartialOld.route).toPrimitiveBundle
  realization inline (@cutRealization Bool Bool instDecidableEqBool Reg.ContractPrototype.Inputs.ValidatedPartialOld.route) := by
    have h : Reg.ContractPrototype.Inputs.ValidatedPartialOld.route = (fun b : Bool => b) := by
      funext b
      unfold Reg.ContractPrototype.Inputs.ValidatedPartialOld.route
      exact @ite_self Bool _ _ b
    exact h.symm ▸ (show LegacyPrimitiveRealization bitArena (Boundary (fun b : Bool => b))
      (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b)) from ⟨Iff.rfl⟩)
  variation bitVariation sensitivity bitSensitivity
  escape from (Bool) escape continues (open)
end
end Reg.ContractPrototype.Controls.ValidatedPartial
