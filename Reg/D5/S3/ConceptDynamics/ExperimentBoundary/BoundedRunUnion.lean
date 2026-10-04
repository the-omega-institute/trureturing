import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
import Reg.Support.BoundedRunSpace



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

theorem _root_.Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena (D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.Boundary fun (b : Bool) => b) (@D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization Bool Bool instDecidableEqBool fun (b : Bool) => b) := by exact ⟨Iff.rfl⟩

attribute [local instance] _root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.instDecidableEqStateBitArena in

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary) (type_of% (bitArena)) (type_of% (bitArena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))) (type_of% (bitVariation)) (type_of% (bitSensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__information_unit,
  realizationName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__primitive_realization,
  realizationSource := none,
  generated := false,
  arena := ⟨(bitArena)⟩,
  objectArena := ⟨(bitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (bitArena) (((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b)))) (((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))).toPrimitiveBundle) ⟨(Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b)),
  variation := some ⟨(bitVariation)⟩,
  sensitivity := some ⟨(bitSensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
