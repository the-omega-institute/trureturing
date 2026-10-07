import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))) (type_of% (Bool)) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__information_unit,
  realizationName := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__primitive_realization,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(bitArena)⟩,
  objectArena := .law ⟨(bitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (bitArena) (((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b)))) (((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))).toPrimitiveBundle) ⟨(Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary.__primitive_realization) (@_root_.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((((@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))).toPrimitiveBundle)).Nonempty; decide),
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b)),
  variation := .evidence ⟨(bitVariation)⟩ (by first | exact (bitVariation) | exact ⟨_, _, (bitVariation)⟩),
  sensitivity := .evidence ⟨(bitSensitivity)⟩ (by exact (bitSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

end

end Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion


noncomputable def Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena
noncomputable def Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"ExperimentBoundary\",\"BoundedRunUnion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"ExperimentBoundary\",\"BoundedRunUnion\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace.bitArena
noncomputable def Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"ExperimentBoundary\",\"BoundedRunUnion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"ExperimentBoundary\",\"BoundedRunUnion\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion, declaration := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
