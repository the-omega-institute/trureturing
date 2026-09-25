import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
import Reg.Support.BoundedRunSpace

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena, theoremName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary,
      statementIdentity := "sha256:f688347ef95d3a1cf53c6f55feb29b319696b0379f090aaf028b0b756d7a0c03",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena, theoremName := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary,
      statementIdentity := "sha256:f688347ef95d3a1cf53c6f55feb29b319696b0379f090aaf028b0b756d7a0c03",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion }

namespace Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
open _root_.D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace
attribute [local instance] _root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.instDecidableEqStateBitArena in

register_information_theorem _root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary in bitArena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))
  primitives ((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))).toPrimitiveBundle
  realization inline ((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))) := by exact ⟨Iff.rfl⟩
  variation bitVariation sensitivity bitSensitivity
  escape from (Bool) escape continues (open)
end

end Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
