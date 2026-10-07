import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Resource.MinimumRetrievalTime
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary
open LeanInformationAudit
open _root_.D5.S3.Resource.MinimumRetrievalTime
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
noncomputable section
universe u v w

private abbrev integralSignature (size : ℕ) : Signature where
  Params := Unit
  State := fun _ => (ℕ → Fin size) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def integralActual (size : ℕ) [NeZero size] : Realization (integralSignature size) :=
  realize (integralSignature size)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples (Fin size))
    (fun impossible => nomatch impossible)

private def integralRejected (size : ℕ) : Realization (integralSignature size) :=
  realize (integralSignature size) (fun _ _ _ => 0) (fun impossible => nomatch impossible)

private theorem integralDependence (size : ℕ) [NeZero size] :
    ObservationalDependence (integralSignature size) (integralActual size) := by
  have : IsProbabilityMeasure (uniformSamples (Fin size)) := by
    dsimp [uniformSamples]
    infer_instance
  intro role
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  simp [integralActual, realize, integral_const]

private def witnessBasis (dimension : ℕ) : Module.Basis (Fin dimension) (ULift.{u} ℚ)
    (ULift.{v} (Fin dimension → ℚ)) :=
  ((Pi.basisFun ℚ (Fin dimension)).mapCoeffs ULift.ringEquiv.symm
    (by intro scalar vector; rfl)).map
    ULift.moduleEquiv.symm

namespace ProbabilityBridge
private abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ value => value.toReal) (fun impossible => nomatch impossible)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun impossible => nomatch impossible)

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {K : Type u} {V : Type v} {alphabet : Type w}
    [Field K] [AddCommGroup V] [Module K V]
    [Fintype alphabet] [Nonempty alphabet] [MeasurableSpace alphabet]
    [MeasurableSingletonClass alphabet]
    (columns : alphabet → V) (file : Submodule K V)
    (hfile : file ≤ Submodule.span K (Set.range columns)),
    Measurable (retrievalTime columns file) ∧
    (∀ (time : ℕ) sample, (time : ℝ≥0∞) < retrievalTime columns file sample ↔
      ¬ recovered columns file time sample) ∧
    (∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet) =
      ∑' time : ℕ, uniformSamples alphabet {sample | ¬ recovered columns file time sample} ∧
    (∀ time : ℕ, uniformSamples alphabet {sample | ¬ recovered columns file time sample} ≤
      (Fintype.card alphabet : ℝ≥0∞) *
        (1 - (Fintype.card alphabet : ℝ≥0∞)⁻¹) ^ time) ∧
    (∀ horizon : ℕ, (∑ time ∈ Finset.range horizon,
      uniformSamples alphabet {sample | ¬ recovered columns file time sample}) ≤
        ∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet) ∧
    (∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet) < ⊤ ∧
    Integrable (fun sample => (retrievalTime columns file sample).toReal)
      (uniformSamples alphabet) ∧
    (∫ sample, (retrievalTime columns file sample).toReal ∂uniformSamples alphabet) =
      observation.readout () ()
        (∫⁻ sample, retrievalTime columns file sample ∂uniformSamples alphabet)

private theorem actualLaw : arena.{u,v,w}.Law actual :=
  @retrieval_time_probability_bridge

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

private theorem rejectedLaw : ¬ arena.{u,v,w}.Law rejected := by
  letI : MeasurableSpace (ULift.{w} Unit) := ⊤
  intro law
  let columns : ULift.{w} Unit → ULift.{v} ℚ := fun _ => 0
  let file : Submodule (ULift.{u} ℚ) (ULift.{v} ℚ) := ⊥
  have htime : ∀ sample, retrievalTime columns file sample = 0 := by
    intro sample
    simp [retrievalTime, minimumTime, recovered, file]
  obtain ⟨_, _, _, _, _, _, _, impossible⟩ := law columns file bot_le
  simp [rejected, realize, htime] at impossible

private def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

noncomputable def registration_2.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.MinimumRetrievalTime.retrieval_time_probability_bridge.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ value => value.toReal)
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "MinimumRetrievalTime") "retrieval_time_probability_bridge") "Reg.D5.S3.Resource.MinimumRetrievalTime/_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") 0) "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") "Auxiliary") "ProbabilityBridge") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ value => value.toReal)
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.MinimumRetrievalTime, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.retrieval_time_probability_bridge, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.sourceBridgeFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.observationFact0, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.anchorEnumeration }


#print axioms registration

end ProbabilityBridge

namespace OldCode
private abbrev arena : Arena where
  signature := integralSignature 4
  Law observation := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V]
    [Module K V] (basis : Module.Basis (Fin 3) K V),
    Submodule.span K (Set.range (oldColumns basis)) = ⊤ ∧
    (∫ sample, (retrievalTime (oldColumns basis) (oldFirstFile basis) sample).toReal
      ∂uniformSamples (Fin 4)) = 2 ∧
    observation.readout () ()
      (fun sample => (retrievalTime (oldColumns basis) (oldSecondFile basis) sample).toReal) = 6

private theorem actualLaw : arena.{u,v}.Law (integralActual 4) :=
  @old_code_actual_expectations

private theorem rejectedLaw : ¬ arena.{u,v}.Law (integralRejected 4) := by
  intro law
  have impossible := (law (witnessBasis.{u,v} 3)).2.2
  norm_num [integralRejected, realize] at impossible

private def registration : Registration arena.{u,v} (arena.Law (integralActual 4)) where
  actual := integralActual 4
  bridge := Iff.rfl
  variation := ⟨actualLaw, integralRejected 4, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨integralRejected 4, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := integralDependence 4

noncomputable def registration_3.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.MinimumRetrievalTime.old_code_actual_expectations.{u_1, u_2}) (type_of% (realize.{0, 0, 0, 0, 0} (integralSignature 4)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 4))
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "MinimumRetrievalTime") "old_code_actual_expectations") "Reg.D5.S3.Resource.MinimumRetrievalTime/_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") 0) "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") "Auxiliary") "OldCode") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} (integralSignature 4)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 4))
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.MinimumRetrievalTime, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.old_code_actual_expectations, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.sourceBridgeFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.observationFact0, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.anchorEnumeration }


#print axioms registration
end OldCode

namespace ThreeKernel
private abbrev arena : Arena where
  signature := integralSignature 5
  Law observation := ∀ {K : Type u} {V : Type v} {W : Type w} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (columns : Fin 5 → V) (file : Submodule K V) (projection : V →ₗ[K] W)
    (first second : V) (hfirst : first ∈ file) (hsecond : second ∈ file)
    (hindependent : LinearIndependent K ![projection first, projection second])
    (left right : Fin 5) (hleftRight : left ≠ right)
    (hzero : ∀ index : Fin 5, index ≠ left → index ≠ right →
      projection (columns index) = 0)
    (hfile : file ≤ Submodule.span K (Set.range columns)),
    6 < observation.readout () () (fun sample => (retrievalTime columns file sample).toReal)

private theorem actualLaw : arena.{u,v,w}.Law (integralActual 5) :=
  @five_column_three_kernel_obstruction

private theorem rejectedLaw : ¬ arena.{u,v,w}.Law (integralRejected 5) := by
  intro law
  let basis := witnessBasis.{u,v} 2
  let outputBasis := witnessBasis.{u,w} 2
  let columns : Fin 5 → ULift.{v} (Fin 2 → ℚ) := ![basis 0, basis 1, 0, 0, 0]
  let projection := basis.constr (ULift.{u} ℚ) outputBasis
  have hindependent : LinearIndependent (ULift.{u} ℚ)
      ![projection (basis 0), projection (basis 1)] := by
    convert outputBasis.linearIndependent using 1
    ext index
    fin_cases index <;> simp [projection]
  have hzero : ∀ index : Fin 5, index ≠ 0 → index ≠ 1 →
      projection (columns index) = 0 := by
    intro index notZero notOne
    fin_cases index
    · exact (notZero rfl).elim
    · exact (notOne rfl).elim
    · exact map_zero projection
    · exact map_zero projection
    · exact map_zero projection
  have hfull : Submodule.span (ULift.{u} ℚ) (Set.range columns) = ⊤ := by
    apply top_unique
    rw [← basis.span_eq]
    apply Submodule.span_mono
    rintro vector ⟨index, rfl⟩
    fin_cases index
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  have impossible := law columns ⊤ projection (basis 0) (basis 1) (by trivial)
    (by trivial) hindependent 0 1 (by decide) hzero (by rw [hfull])
  norm_num [integralRejected, realize] at impossible

private def registration : Registration arena.{u,v,w} (arena.Law (integralActual 5)) where
  actual := integralActual 5
  bridge := Iff.rfl
  variation := ⟨actualLaw, integralRejected 5, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨integralRejected 5, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := integralDependence 5

noncomputable def registration_4.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.MinimumRetrievalTime.five_column_three_kernel_obstruction.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 5))
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "MinimumRetrievalTime") "five_column_three_kernel_obstruction") "Reg.D5.S3.Resource.MinimumRetrievalTime/_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") 0) "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") "Auxiliary") "ThreeKernel") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 5))
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.MinimumRetrievalTime, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_three_kernel_obstruction, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.sourceBridgeFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.observationFact0, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.anchorEnumeration }


#print axioms registration
end ThreeKernel

namespace BadPairs
private abbrev arena : Arena where
  signature := integralSignature 5
  Law observation := ∀ {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V] (columns : Fin 5 → V) (file : Submodule K V)
    (common left right : Fin 5) (hcommonLeft : common ≠ left)
    (hcommonRight : common ≠ right) (hleftRight : left ≠ right)
    (hbadLeft : ¬ file ≤ Submodule.span K ({columns common, columns left} : Set V))
    (hbadRight : ¬ file ≤ Submodule.span K ({columns common, columns right} : Set V))
    (hfile : file ≤ Submodule.span K (Set.range columns)),
    2 < observation.readout () () (fun sample => (retrievalTime columns file sample).toReal)

private theorem actualLaw : arena.{u,v}.Law (integralActual 5) :=
  @five_column_bad_pairs_obstruction

private theorem rejectedLaw : ¬ arena.{u,v}.Law (integralRejected 5) := by
  intro law
  let basis := witnessBasis.{u,v} 3
  let columns : Fin 5 → ULift.{v} (Fin 3 → ℚ) := ![basis 0, basis 1, basis 2, 0, 0]
  let file : Submodule (ULift.{u} ℚ) (ULift.{v} (Fin 3 → ℚ)) :=
    Submodule.span _ ({basis 0} : Set _)
  have hbadLeft : ¬ file ≤ Submodule.span _ ({columns 1, columns 2} : Set _) := by
    intro inclusion
    have member := inclusion (Submodule.subset_span (Set.mem_singleton (basis 0)))
    obtain ⟨left, right, equation⟩ := Submodule.mem_span_pair.mp member
    have impossible := congrArg (basis.coord 0) equation
    simp [columns, map_add, map_smul, Module.Basis.coord_apply] at impossible
  have hbadRight : ¬ file ≤ Submodule.span _ ({columns 1, columns 3} : Set _) := by
    intro inclusion
    have member := inclusion (Submodule.subset_span (Set.mem_singleton (basis 0)))
    obtain ⟨left, right, equation⟩ := Submodule.mem_span_pair.mp member
    have impossible := congrArg (basis.coord 0) equation
    simp [columns, map_add, map_smul, Module.Basis.coord_apply] at impossible
  have hfile : file ≤ Submodule.span _ (Set.range columns) := by
    apply Submodule.span_mono
    intro vector member
    rcases Set.mem_singleton_iff.mp member with rfl
    exact ⟨0, rfl⟩
  have impossible := law columns file 1 2 3 (by decide) (by decide) (by decide)
    hbadLeft hbadRight hfile
  norm_num [integralRejected, realize] at impossible

private def registration : Registration arena.{u,v} (arena.Law (integralActual 5)) where
  actual := integralActual 5
  bridge := Iff.rfl
  variation := ⟨actualLaw, integralRejected 5, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨integralRejected 5, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := integralDependence 5

noncomputable def registration_5.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.MinimumRetrievalTime.five_column_bad_pairs_obstruction.{u_1, u_2}) (type_of% (realize.{0, 0, 0, 0, 0} (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 5))
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "MinimumRetrievalTime") "five_column_bad_pairs_obstruction") "Reg.D5.S3.Resource.MinimumRetrievalTime/_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") 0) "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") "Auxiliary") "BadPairs") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 5))
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.MinimumRetrievalTime, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_bad_pairs_obstruction, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalObjectArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.sourceBridgeFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.observationFact0, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.anchorEnumeration }


#print axioms registration
end BadPairs

namespace Projected
private abbrev arena : Arena where
  signature := integralSignature 5
  Law observation := ∀ {K : Type u} {V : Type v} {W : Type w} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (columns : Fin 5 → V) (file : Submodule K V) (projection : V →ₗ[K] W)
    (target : V) (htarget : target ∈ file) (htargetNe : target ≠ 0)
    (htargetProjection : projection target = 0)
    (left right third : Fin 5) (hleftRight : left ≠ right)
    (hleftThird : left ≠ third) (hrightThird : right ≠ third)
    (hindependent : LinearIndependent K ![projection (columns left), projection (columns right)])
    (hthird : target ∉ Submodule.span K ({columns third} : Set V))
    (hfile : file ≤ Submodule.span K (Set.range columns)),
    2 < observation.readout () () (fun sample => (retrievalTime columns file sample).toReal)

private theorem actualLaw : arena.{u,v,w}.Law (integralActual 5) :=
  @five_column_projected_obstruction

private theorem rejectedLaw : ¬ arena.{u,v,w}.Law (integralRejected 5) := by
  intro law
  let basis := witnessBasis.{u,v} 3
  let outputBasis := witnessBasis.{u,w} 2
  let columns : Fin 5 → ULift.{v} (Fin 3 → ℚ) :=
    ![basis 1, basis 2, basis 1 + basis 2, basis 0, 0]
  let projection := basis.constr (ULift.{u} ℚ) ![0, outputBasis 0, outputBasis 1]
  let file : Submodule (ULift.{u} ℚ) (ULift.{v} (Fin 3 → ℚ)) :=
    Submodule.span _ ({basis 0} : Set _)
  have hindependent : LinearIndependent (ULift.{u} ℚ)
      ![projection (columns 0), projection (columns 1)] := by
    convert outputBasis.linearIndependent using 1
    ext index
    fin_cases index <;> simp [projection, columns]
  have hthird : basis 0 ∉ Submodule.span (ULift.{u} ℚ) ({columns 2} : Set _) := by
    intro member
    obtain ⟨scalar, equation⟩ := Submodule.mem_span_singleton.mp member
    have impossible := congrArg (basis.coord 0) equation
    simp [columns, map_add, map_smul, Module.Basis.coord_apply] at impossible
  have hfile : file ≤ Submodule.span _ (Set.range columns) := by
    apply Submodule.span_mono
    intro vector member
    rcases Set.mem_singleton_iff.mp member with rfl
    exact ⟨3, rfl⟩
  have impossible := law columns file projection (basis 0)
    (Submodule.subset_span (Set.mem_singleton (basis 0))) (basis.ne_zero 0)
    (by simp [projection]) 0 1 2 (by decide) (by decide) (by decide)
    hindependent hthird hfile
  norm_num [integralRejected, realize] at impossible

private def registration : Registration arena.{u,v,w} (arena.Law (integralActual 5)) where
  actual := integralActual 5
  bridge := Iff.rfl
  variation := ⟨actualLaw, integralRejected 5, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨integralRejected 5, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := integralDependence 5

noncomputable def registration_6.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.MinimumRetrievalTime.five_column_projected_obstruction.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 5))
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "MinimumRetrievalTime") "five_column_projected_obstruction") "Reg.D5.S3.Resource.MinimumRetrievalTime/_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") 0) "Reg") "D5") "S3") "Resource") "MinimumRetrievalTime") "Auxiliary") "Projected") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples.{0} (Fin 5))
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.MinimumRetrievalTime, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_projected_obstruction, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalObjectArenaFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.sourceBridgeFact, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.observationFact0, `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.anchorEnumeration }


#print axioms registration
end Projected

namespace Universal
private abbrev signature : Signature where
  Params := Unit
  State := fun _ => (ℕ → Fin 5) → ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature := realize signature
  (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples (Fin 5))
  (fun impossible => nomatch impossible)

private def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun impossible => nomatch impossible)

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V] (basis : Module.Basis (Fin 3) K V)
    (columns : Fin 5 → V) (hfull : Submodule.span K (Set.range columns) = ⊤),
    (2 < observation.readout 0 ()
      (fun sample => (retrievalTime columns (oldFirstFile basis) sample).toReal)) ∨
    (6 < observation.readout 1 ()
      (fun sample => (retrievalTime columns (oldSecondFile basis) sample).toReal))

private theorem actualLaw : arena.{u,v}.Law actual :=
  @five_column_universal_obstruction

private theorem dependence : ObservationalDependence signature actual := by
  have : IsProbabilityMeasure (uniformSamples (Fin 5)) := by
    dsimp [uniformSamples]
    infer_instance
  intro role
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  simp [actual, realize, integral_const]

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  let basis := witnessBasis.{u,v} 3
  let columns : Fin 5 → ULift.{v} (Fin 3 → ℚ) := ![basis 0, basis 1, basis 2, 0, 0]
  have hfull : Submodule.span (ULift.{u} ℚ) (Set.range columns) = ⊤ := by
    apply top_unique
    rw [← basis.span_eq]
    apply Submodule.span_mono
    rintro vector ⟨index, rfl⟩
    fin_cases index
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have impossible := law basis columns hfull
  norm_num [rejected, realize] at impossible

private theorem variation : Variation arena.{u,v} actual :=
  ⟨actualLaw, rejected, rejectedLaw⟩

private theorem rejectedChangesEveryRole (role : Fin 2) :
    actual.readout role ≠ rejected.readout role := by
  have : IsProbabilityMeasure (uniformSamples (Fin 5)) := by
    dsimp [uniformSamples]
    infer_instance
  intro equality
  have impossible := congrFun (congrFun equality ()) (fun _ => (1 : ℝ))
  norm_num [actual, rejected, realize, integral_const] at impossible

private def selection : _root_.Reg.Support.SourceSelection := {
  owner := `D5.S3.Resource.MinimumRetrievalTime
  coordinates := #[]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateOperand := some #["arg"] },
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateOperand := some #["arg"] }] }

#print axioms variation
#print axioms dependence
#print axioms rejectedChangesEveryRole
end Universal

#print axioms ProbabilityBridge.actualLaw
#print axioms ProbabilityBridge.dependence
#print axioms ThreeKernel.actualLaw
#print axioms BadPairs.actualLaw
#print axioms Projected.actualLaw
#print axioms Universal.actualLaw
end
end Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary


noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena.{u_1,
  u_2, u_3}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena.{u_1,
  u_2, u_3}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena.{u_1,
  u_2}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena.{u_1,
  u_2}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena.{u_1,
  u_2, u_3}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena.{u_1,
  u_2, u_3}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena.{u_1,
  u_2, u_3}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena.{u_1,
  u_2, u_3}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena.{u_1,
  u_2}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena.{u_1,
  u_2}
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena.{u_1,
    u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena.{u_1,
      u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena.{u_1,
        u_2, u_3}
      (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration.{u_1,
      u_2, u_3})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_projected_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_projected_obstruction, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena.{u_1,
    u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.arena.{u_1,
      u_2, u_3}
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration.{u_1,
    u_2, u_3})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.observation0.{u_1, u_2, u_3} : {K : Type u_1} →
  {V : Type u_2} →
    {W : Type u_3} →
      [inst : Field.{u_1} K] →
        [inst_1 : AddCommGroup.{u_2} V] →
          [inst_2 :
              @Module.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)] →
            [inst_3 : AddCommGroup.{u_3} W] →
              [inst_4 :
                  @Module.{u_1, u_3} K W
                    (@DivisionSemiring.toSemiring.{u_1} K
                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                    (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3)] →
                (columns : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → V) →
                  (file :
                      @Submodule.{u_1, u_2} K V
                        (@DivisionSemiring.toSemiring.{u_1} K
                          (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2) →
                    (projection :
                        @LinearMap.{u_1, u_1, u_2, u_3} K K
                          (@DivisionSemiring.toSemiring.{u_1} K
                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                          (@DivisionSemiring.toSemiring.{u_1} K
                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                          (@RingHom.id.{u_1} K
                            (@Semiring.toNonAssocSemiring.{u_1} K
                              (@DivisionSemiring.toSemiring.{u_1} K
                                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
                          V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                          (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4) →
                      (target : V) →
                        (htarget :
                            @Membership.mem.{u_2, u_2} V
                              (@Submodule.{u_1, u_2} K V
                                (@DivisionSemiring.toSemiring.{u_1} K
                                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                              (@SetLike.instMembership.{u_2, u_2}
                                (@Submodule.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                V
                                (@Submodule.setLike.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
                              file target) →
                          (htargetNe :
                              @Ne.{u_2 + 1} V target
                                (@OfNat.ofNat.{u_2} V (nat_lit 0)
                                  (@Zero.toOfNat0.{u_2} V
                                    (@NegZeroClass.toZero.{u_2} V
                                      (@SubNegZeroMonoid.toNegZeroClass.{u_2} V
                                        (@SubtractionMonoid.toSubNegZeroMonoid.{u_2} V
                                          (@SubtractionCommMonoid.toSubtractionMonoid.{u_2} V
                                            (@AddCommGroup.toDivisionAddCommMonoid.{u_2} V inst_1)))))))) →
                            (htargetProjection :
                                @Eq.{u_3 + 1} W
                                  (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
                                    (@LinearMap.{u_1, u_1, u_2, u_3} K K
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@RingHom.id.{u_1} K
                                        (@Semiring.toNonAssocSemiring.{u_1} K
                                          (@DivisionSemiring.toSemiring.{u_1} K
                                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
                                      V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                      (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
                                    V (fun (x : V) => W)
                                    (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                      (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4
                                      (@RingHom.id.{u_1} K
                                        (@Semiring.toNonAssocSemiring.{u_1} K
                                          (@DivisionSemiring.toSemiring.{u_1} K
                                            (@Semifield.toDivisionSemiring.{u_1} K
                                              (@Field.toSemifield.{u_1} K inst))))))
                                    projection target)
                                  (@OfNat.ofNat.{u_3} W (nat_lit 0)
                                    (@Zero.toOfNat0.{u_3} W
                                      (@NegZeroClass.toZero.{u_3} W
                                        (@SubNegZeroMonoid.toNegZeroClass.{u_3} W
                                          (@SubtractionMonoid.toSubNegZeroMonoid.{u_3} W
                                            (@SubtractionCommMonoid.toSubtractionMonoid.{u_3} W
                                              (@AddCommGroup.toDivisionAddCommMonoid.{u_3} W inst_3)))))))) →
                              (left right third : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
                                (hleftRight :
                                    @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left
                                      right) →
                                  (hleftThird :
                                      @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left
                                        third) →
                                    (hrightThird :
                                        @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                          right third) →
                                      (hindependent :
                                          @LinearIndependent.{0, u_1, u_3}
                                            (Fin
                                              (Nat.succ
                                                (Nat.succ
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                            K W
                                            (@Matrix.vecCons.{u_3} W
                                              (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                              (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
                                                (@LinearMap.{u_1, u_1, u_2, u_3} K K
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@RingHom.id.{u_1} K
                                                    (@Semiring.toNonAssocSemiring.{u_1} K
                                                      (@DivisionSemiring.toSemiring.{u_1} K
                                                        (@Semifield.toDivisionSemiring.{u_1} K
                                                          (@Field.toSemifield.{u_1} K inst)))))
                                                  V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                                  (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
                                                V (fun (x : V) => W)
                                                (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                                  (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4
                                                  (@RingHom.id.{u_1} K
                                                    (@Semiring.toNonAssocSemiring.{u_1} K
                                                      (@DivisionSemiring.toSemiring.{u_1} K
                                                        (@Semifield.toDivisionSemiring.{u_1} K
                                                          (@Field.toSemifield.{u_1} K inst))))))
                                                projection (columns left))
                                              (@Matrix.vecCons.{u_3} W
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
                                                  (@LinearMap.{u_1, u_1, u_2, u_3} K K
                                                    (@DivisionSemiring.toSemiring.{u_1} K
                                                      (@Semifield.toDivisionSemiring.{u_1} K
                                                        (@Field.toSemifield.{u_1} K inst)))
                                                    (@DivisionSemiring.toSemiring.{u_1} K
                                                      (@Semifield.toDivisionSemiring.{u_1} K
                                                        (@Field.toSemifield.{u_1} K inst)))
                                                    (@RingHom.id.{u_1} K
                                                      (@Semiring.toNonAssocSemiring.{u_1} K
                                                        (@DivisionSemiring.toSemiring.{u_1} K
                                                          (@Semifield.toDivisionSemiring.{u_1} K
                                                            (@Field.toSemifield.{u_1} K inst)))))
                                                    V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                                    (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
                                                  V (fun (x : V) => W)
                                                  (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                                                    (@DivisionSemiring.toSemiring.{u_1} K
                                                      (@Semifield.toDivisionSemiring.{u_1} K
                                                        (@Field.toSemifield.{u_1} K inst)))
                                                    (@DivisionSemiring.toSemiring.{u_1} K
                                                      (@Semifield.toDivisionSemiring.{u_1} K
                                                        (@Field.toSemifield.{u_1} K inst)))
                                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                                    (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4
                                                    (@RingHom.id.{u_1} K
                                                      (@Semiring.toNonAssocSemiring.{u_1} K
                                                        (@DivisionSemiring.toSemiring.{u_1} K
                                                          (@Semifield.toDivisionSemiring.{u_1} K
                                                            (@Field.toSemifield.{u_1} K inst))))))
                                                  projection (columns right))
                                                (@Matrix.vecEmpty.{u_3} W)))
                                            (@DivisionSemiring.toSemiring.{u_1} K
                                              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                            (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_4) →
                                        (hthird :
                                            Not
                                              (@Membership.mem.{u_2, u_2} V
                                                (@Submodule.{u_1, u_2} K V
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                                (@SetLike.instMembership.{u_2, u_2}
                                                  (@Submodule.{u_1, u_2} K V
                                                    (@DivisionSemiring.toSemiring.{u_1} K
                                                      (@Semifield.toDivisionSemiring.{u_1} K
                                                        (@Field.toSemifield.{u_1} K inst)))
                                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                                  V
                                                  (@Submodule.setLike.{u_1, u_2} K V
                                                    (@DivisionSemiring.toSemiring.{u_1} K
                                                      (@Semifield.toDivisionSemiring.{u_1} K
                                                        (@Field.toSemifield.{u_1} K inst)))
                                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
                                                (@Submodule.span.{u_1, u_2} K V
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
                                                  (@Singleton.singleton.{u_2, u_2} V (Set.{u_2} V)
                                                    (@Set.instSingletonSet.{u_2} V) (columns third)))
                                                target)) →
                                          (hfile :
                                              @LE.le.{u_2}
                                                (@Submodule.{u_1, u_2} K V
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                                (@Preorder.toLE.{u_2}
                                                  (@Submodule.{u_1, u_2} K V
                                                    (@DivisionSemiring.toSemiring.{u_1} K
                                                      (@Semifield.toDivisionSemiring.{u_1} K
                                                        (@Field.toSemifield.{u_1} K inst)))
                                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                                  (@PartialOrder.toPreorder.{u_2}
                                                    (@Submodule.{u_1, u_2} K V
                                                      (@DivisionSemiring.toSemiring.{u_1} K
                                                        (@Semifield.toDivisionSemiring.{u_1} K
                                                          (@Field.toSemifield.{u_1} K inst)))
                                                      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                                    (@Submodule.instPartialOrder.{u_1, u_2} K V
                                                      (@DivisionSemiring.toSemiring.{u_1} K
                                                        (@Semifield.toDivisionSemiring.{u_1} K
                                                          (@Field.toSemifield.{u_1} K inst)))
                                                      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
                                                file
                                                (@Submodule.span.{u_1, u_2} K V
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
                                                  (@Set.range.{u_2, 1} V
                                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                                    columns))) →
                                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0,
                                                0, 0, 0, 0}
                                              (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                              PUnit.unit.{1} PUnit.unit.{1} :=
  fun {K : Type u_1} {V : Type u_2} {W : Type u_3} [inst : Field.{u_1} K] [inst_1 : AddCommGroup.{u_2} V]
    [inst_2 :
      @Module.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)]
    [AddCommGroup.{u_3} W]
    [@Module.{u_1, u_3} K W
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3)]
    (columns : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → V)
    (file :
      @Submodule.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
    (projection :
      @LinearMap.{u_1, u_1, u_2, u_3} K K
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@RingHom.id.{u_1} K
          (@Semiring.toNonAssocSemiring.{u_1} K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
        V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
    (target : V)
    (htarget :
      @Membership.mem.{u_2, u_2} V
        (@Submodule.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
        (@SetLike.instMembership.{u_2, u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          V
          (@Submodule.setLike.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
        file target)
    (htargetNe :
      @Ne.{u_2 + 1} V target
        (@OfNat.ofNat.{u_2} V (nat_lit 0)
          (@Zero.toOfNat0.{u_2} V
            (@NegZeroClass.toZero.{u_2} V
              (@SubNegZeroMonoid.toNegZeroClass.{u_2} V
                (@SubtractionMonoid.toSubNegZeroMonoid.{u_2} V
                  (@SubtractionCommMonoid.toSubtractionMonoid.{u_2} V
                    (@AddCommGroup.toDivisionAddCommMonoid.{u_2} V inst_1))))))))
    (htargetProjection :
      @Eq.{u_3 + 1} W
        (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
          (@LinearMap.{u_1, u_1, u_2, u_3} K K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@RingHom.id.{u_1} K
              (@Semiring.toNonAssocSemiring.{u_1} K
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
            V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
            inst_4)
          V (fun (x : V) => W)
          (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4
            (@RingHom.id.{u_1} K
              (@Semiring.toNonAssocSemiring.{u_1} K
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
          projection target)
        (@OfNat.ofNat.{u_3} W (nat_lit 0)
          (@Zero.toOfNat0.{u_3} W
            (@NegZeroClass.toZero.{u_3} W
              (@SubNegZeroMonoid.toNegZeroClass.{u_3} W
                (@SubtractionMonoid.toSubNegZeroMonoid.{u_3} W
                  (@SubtractionCommMonoid.toSubtractionMonoid.{u_3} W
                    (@AddCommGroup.toDivisionAddCommMonoid.{u_3} W inst_3))))))))
    (left right third : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (hleftRight : @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left right)
    (hleftThird : @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left third)
    (hrightThird : @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) right third)
    (hindependent :
      @LinearIndependent.{0, u_1, u_3}
        (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) K W
        (@Matrix.vecCons.{u_3} W (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
            (@LinearMap.{u_1, u_1, u_2, u_3} K K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@RingHom.id.{u_1} K
                (@Semiring.toNonAssocSemiring.{u_1} K
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
              V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
              inst_4)
            V (fun (x : V) => W)
            (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
              inst_4
              (@RingHom.id.{u_1} K
                (@Semiring.toNonAssocSemiring.{u_1} K
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
            projection (columns left))
          (@Matrix.vecCons.{u_3} W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
              (@LinearMap.{u_1, u_1, u_2, u_3} K K
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@RingHom.id.{u_1} K
                  (@Semiring.toNonAssocSemiring.{u_1} K
                    (@DivisionSemiring.toSemiring.{u_1} K
                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
                V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
                inst_4)
              V (fun (x : V) => W)
              (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
                inst_4
                (@RingHom.id.{u_1} K
                  (@Semiring.toNonAssocSemiring.{u_1} K
                    (@DivisionSemiring.toSemiring.{u_1} K
                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
              projection (columns right))
            (@Matrix.vecEmpty.{u_3} W)))
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_4)
    (hthird :
      Not
        (@Membership.mem.{u_2, u_2} V
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          (@SetLike.instMembership.{u_2, u_2}
            (@Submodule.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
            V
            (@Submodule.setLike.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
          (@Submodule.span.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
            (@Singleton.singleton.{u_2, u_2} V (Set.{u_2} V) (@Set.instSingletonSet.{u_2} V) (columns third)))
          target))
    (hfile :
      @LE.le.{u_2}
        (@Submodule.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
        (@Preorder.toLE.{u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          (@PartialOrder.toPreorder.{u_2}
            (@Submodule.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
            (@Submodule.instPartialOrder.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
        file
        (@Submodule.span.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
          (@Set.range.{u_2, 1} V (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) columns))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration._proof_1)
    PUnit.unit.{1} PUnit.unit.{1}
    fun (sample : Nat → Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) =>
    ENNReal.toReal
      (@D5.S3.Resource.MinimumRetrievalTime.retrievalTime.{u_1, u_2, 0} K V
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) inst inst_1 inst_2 columns file sample)

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_projected_obstruction\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_projected_obstruction, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_projected_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_projected_obstruction, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration.{u_1,
  u_2, u_3}).actual (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration.{u_1,
  u_2, u_3}).variation.2.choose (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration.{u_1,
  u_2, u_3}).variation.1 (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration.{u_1,
  u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"Projected\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.Projected.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena.{u_1,
    u_2}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena.{u_1,
      u_2}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena.{u_1,
        u_2}
      (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration.{u_1,
      u_2})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"old_code_actual_expectations\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.old_code_actual_expectations, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena.{u_1,
    u_2}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.arena.{u_1,
      u_2}
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration.{u_1,
    u_2})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.observation0.{u_1, u_2} : {K : Type u_1} →
  {V : Type u_2} →
    [inst : Field.{u_1} K] →
      [inst_1 : AddCommGroup.{u_2} V] →
        [inst_2 :
            @Module.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)] →
          (basis :
              @Module.Basis.{0, u_1, u_2} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              PUnit.unit.{1} PUnit.unit.{1} :=
  fun {K : Type u_1} {V : Type u_2} [inst : Field.{u_1} K] [inst_1 : AddCommGroup.{u_2} V]
    [inst_2 :
      @Module.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)]
    (basis :
      @Module.Basis.{0, u_1, u_2} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration._proof_1)
    PUnit.unit.{1} PUnit.unit.{1}
    fun (sample : Nat → Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    ENNReal.toReal
      (@D5.S3.Resource.MinimumRetrievalTime.retrievalTime.{u_1, u_2, 0} K V
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) inst inst_1 inst_2
        (@D5.S3.Resource.MinimumRetrievalTime.oldColumns.{u_1, u_2} K V inst inst_1 inst_2 basis)
        (@D5.S3.Resource.MinimumRetrievalTime.oldSecondFile.{u_1, u_2} K V inst inst_1 inst_2 basis) sample)

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"old_code_actual_expectations\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.old_code_actual_expectations, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"old_code_actual_expectations\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.old_code_actual_expectations, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration.{u_1,
  u_2}).actual (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration.{u_1,
  u_2}).variation.2.choose (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration.{u_1,
  u_2}).variation.1 (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration.{u_1,
  u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"OldCode\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.OldCode.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena.{u_1,
    u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena.{u_1,
      u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena.{u_1,
        u_2, u_3}
      (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration.{u_1,
      u_2, u_3})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_three_kernel_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_three_kernel_obstruction, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena.{u_1,
    u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.arena.{u_1,
      u_2, u_3}
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration.{u_1,
    u_2, u_3})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.observation0.{u_1, u_2, u_3} : {K : Type u_1} →
  {V : Type u_2} →
    {W : Type u_3} →
      [inst : Field.{u_1} K] →
        [inst_1 : AddCommGroup.{u_2} V] →
          [inst_2 :
              @Module.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)] →
            [inst_3 : AddCommGroup.{u_3} W] →
              [inst_4 :
                  @Module.{u_1, u_3} K W
                    (@DivisionSemiring.toSemiring.{u_1} K
                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                    (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3)] →
                (columns : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → V) →
                  (file :
                      @Submodule.{u_1, u_2} K V
                        (@DivisionSemiring.toSemiring.{u_1} K
                          (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2) →
                    (projection :
                        @LinearMap.{u_1, u_1, u_2, u_3} K K
                          (@DivisionSemiring.toSemiring.{u_1} K
                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                          (@DivisionSemiring.toSemiring.{u_1} K
                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                          (@RingHom.id.{u_1} K
                            (@Semiring.toNonAssocSemiring.{u_1} K
                              (@DivisionSemiring.toSemiring.{u_1} K
                                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
                          V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                          (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4) →
                      (first second : V) →
                        (hfirst :
                            @Membership.mem.{u_2, u_2} V
                              (@Submodule.{u_1, u_2} K V
                                (@DivisionSemiring.toSemiring.{u_1} K
                                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                              (@SetLike.instMembership.{u_2, u_2}
                                (@Submodule.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                V
                                (@Submodule.setLike.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
                              file first) →
                          (hsecond :
                              @Membership.mem.{u_2, u_2} V
                                (@Submodule.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                (@SetLike.instMembership.{u_2, u_2}
                                  (@Submodule.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                  V
                                  (@Submodule.setLike.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
                                file second) →
                            (hindependent :
                                @LinearIndependent.{0, u_1, u_3}
                                  (Fin
                                    (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                  K W
                                  (@Matrix.vecCons.{u_3} W
                                    (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
                                      (@LinearMap.{u_1, u_1, u_2, u_3} K K
                                        (@DivisionSemiring.toSemiring.{u_1} K
                                          (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                        (@DivisionSemiring.toSemiring.{u_1} K
                                          (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                        (@RingHom.id.{u_1} K
                                          (@Semiring.toNonAssocSemiring.{u_1} K
                                            (@DivisionSemiring.toSemiring.{u_1} K
                                              (@Semifield.toDivisionSemiring.{u_1} K
                                                (@Field.toSemifield.{u_1} K inst)))))
                                        V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                        (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
                                      V (fun (x : V) => W)
                                      (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                                        (@DivisionSemiring.toSemiring.{u_1} K
                                          (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                        (@DivisionSemiring.toSemiring.{u_1} K
                                          (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                        (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4
                                        (@RingHom.id.{u_1} K
                                          (@Semiring.toNonAssocSemiring.{u_1} K
                                            (@DivisionSemiring.toSemiring.{u_1} K
                                              (@Semifield.toDivisionSemiring.{u_1} K
                                                (@Field.toSemifield.{u_1} K inst))))))
                                      projection first)
                                    (@Matrix.vecCons.{u_3} W
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
                                        (@LinearMap.{u_1, u_1, u_2, u_3} K K
                                          (@DivisionSemiring.toSemiring.{u_1} K
                                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                          (@DivisionSemiring.toSemiring.{u_1} K
                                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                          (@RingHom.id.{u_1} K
                                            (@Semiring.toNonAssocSemiring.{u_1} K
                                              (@DivisionSemiring.toSemiring.{u_1} K
                                                (@Semifield.toDivisionSemiring.{u_1} K
                                                  (@Field.toSemifield.{u_1} K inst)))))
                                          V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                          (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
                                        V (fun (x : V) => W)
                                        (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                                          (@DivisionSemiring.toSemiring.{u_1} K
                                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                          (@DivisionSemiring.toSemiring.{u_1} K
                                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                          (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4
                                          (@RingHom.id.{u_1} K
                                            (@Semiring.toNonAssocSemiring.{u_1} K
                                              (@DivisionSemiring.toSemiring.{u_1} K
                                                (@Semifield.toDivisionSemiring.{u_1} K
                                                  (@Field.toSemifield.{u_1} K inst))))))
                                        projection second)
                                      (@Matrix.vecEmpty.{u_3} W)))
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_4) →
                              (left right : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
                                (hleftRight :
                                    @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left
                                      right) →
                                  (hzero :
                                      ∀ (index : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
                                        @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                            index left →
                                          @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                              index right →
                                            @Eq.{u_3 + 1} W
                                              (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
                                                (@LinearMap.{u_1, u_1, u_2, u_3} K K
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@RingHom.id.{u_1} K
                                                    (@Semiring.toNonAssocSemiring.{u_1} K
                                                      (@DivisionSemiring.toSemiring.{u_1} K
                                                        (@Semifield.toDivisionSemiring.{u_1} K
                                                          (@Field.toSemifield.{u_1} K inst)))))
                                                  V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                                  (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
                                                V (fun (x : V) => W)
                                                (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@DivisionSemiring.toSemiring.{u_1} K
                                                    (@Semifield.toDivisionSemiring.{u_1} K
                                                      (@Field.toSemifield.{u_1} K inst)))
                                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)
                                                  (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4
                                                  (@RingHom.id.{u_1} K
                                                    (@Semiring.toNonAssocSemiring.{u_1} K
                                                      (@DivisionSemiring.toSemiring.{u_1} K
                                                        (@Semifield.toDivisionSemiring.{u_1} K
                                                          (@Field.toSemifield.{u_1} K inst))))))
                                                projection (columns index))
                                              (@OfNat.ofNat.{u_3} W (nat_lit 0)
                                                (@Zero.toOfNat0.{u_3} W
                                                  (@NegZeroClass.toZero.{u_3} W
                                                    (@SubNegZeroMonoid.toNegZeroClass.{u_3} W
                                                      (@SubtractionMonoid.toSubNegZeroMonoid.{u_3} W
                                                        (@SubtractionCommMonoid.toSubtractionMonoid.{u_3} W
                                                          (@AddCommGroup.toDivisionAddCommMonoid.{u_3} W
                                                            inst_3)))))))) →
                                    (hfile :
                                        @LE.le.{u_2}
                                          (@Submodule.{u_1, u_2} K V
                                            (@DivisionSemiring.toSemiring.{u_1} K
                                              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                          (@Preorder.toLE.{u_2}
                                            (@Submodule.{u_1, u_2} K V
                                              (@DivisionSemiring.toSemiring.{u_1} K
                                                (@Semifield.toDivisionSemiring.{u_1} K
                                                  (@Field.toSemifield.{u_1} K inst)))
                                              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                            (@PartialOrder.toPreorder.{u_2}
                                              (@Submodule.{u_1, u_2} K V
                                                (@DivisionSemiring.toSemiring.{u_1} K
                                                  (@Semifield.toDivisionSemiring.{u_1} K
                                                    (@Field.toSemifield.{u_1} K inst)))
                                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                              (@Submodule.instPartialOrder.{u_1, u_2} K V
                                                (@DivisionSemiring.toSemiring.{u_1} K
                                                  (@Semifield.toDivisionSemiring.{u_1} K
                                                    (@Field.toSemifield.{u_1} K inst)))
                                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
                                          file
                                          (@Submodule.span.{u_1, u_2} K V
                                            (@DivisionSemiring.toSemiring.{u_1} K
                                              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
                                            (@Set.range.{u_2, 1} V
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                              columns))) →
                                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0,
                                          0, 0}
                                        (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                        PUnit.unit.{1} PUnit.unit.{1} :=
  fun {K : Type u_1} {V : Type u_2} {W : Type u_3} [inst : Field.{u_1} K] [inst_1 : AddCommGroup.{u_2} V]
    [inst_2 :
      @Module.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)]
    [AddCommGroup.{u_3} W]
    [@Module.{u_1, u_3} K W
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3)]
    (columns : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → V)
    (file :
      @Submodule.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
    (projection :
      @LinearMap.{u_1, u_1, u_2, u_3} K K
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@RingHom.id.{u_1} K
          (@Semiring.toNonAssocSemiring.{u_1} K
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
        V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2 inst_4)
    (first second : V)
    (hfirst :
      @Membership.mem.{u_2, u_2} V
        (@Submodule.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
        (@SetLike.instMembership.{u_2, u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          V
          (@Submodule.setLike.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
        file first)
    (hsecond :
      @Membership.mem.{u_2, u_2} V
        (@Submodule.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
        (@SetLike.instMembership.{u_2, u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          V
          (@Submodule.setLike.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2))
        file second)
    (hindependent :
      @LinearIndependent.{0, u_1, u_3}
        (Fin (Nat.succ (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) K W
        (@Matrix.vecCons.{u_3} W (Nat.succ (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
            (@LinearMap.{u_1, u_1, u_2, u_3} K K
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@RingHom.id.{u_1} K
                (@Semiring.toNonAssocSemiring.{u_1} K
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
              V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
              inst_4)
            V (fun (x : V) => W)
            (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
              inst_4
              (@RingHom.id.{u_1} K
                (@Semiring.toNonAssocSemiring.{u_1} K
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
            projection first)
          (@Matrix.vecCons.{u_3} W (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
              (@LinearMap.{u_1, u_1, u_2, u_3} K K
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@RingHom.id.{u_1} K
                  (@Semiring.toNonAssocSemiring.{u_1} K
                    (@DivisionSemiring.toSemiring.{u_1} K
                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
                V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
                inst_4)
              V (fun (x : V) => W)
              (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
                inst_4
                (@RingHom.id.{u_1} K
                  (@Semiring.toNonAssocSemiring.{u_1} K
                    (@DivisionSemiring.toSemiring.{u_1} K
                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
              projection second)
            (@Matrix.vecEmpty.{u_3} W)))
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_4)
    (left right : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (hleftRight : @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left right)
    (hzero :
      ∀ (index : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
        @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) index left →
          @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) index right →
            @Eq.{u_3 + 1} W
              (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
                (@LinearMap.{u_1, u_1, u_2, u_3} K K
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                  (@RingHom.id.{u_1} K
                    (@Semiring.toNonAssocSemiring.{u_1} K
                      (@DivisionSemiring.toSemiring.{u_1} K
                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))))
                  V W (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3)
                  inst_2 inst_4)
                V (fun (x : V) => W)
                (@LinearMap.instFunLike.{u_1, u_1, u_2, u_3} K K V W
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) (@AddCommGroup.toAddCommMonoid.{u_3} W inst_3) inst_2
                  inst_4
                  (@RingHom.id.{u_1} K
                    (@Semiring.toNonAssocSemiring.{u_1} K
                      (@DivisionSemiring.toSemiring.{u_1} K
                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst))))))
                projection (columns index))
              (@OfNat.ofNat.{u_3} W (nat_lit 0)
                (@Zero.toOfNat0.{u_3} W
                  (@NegZeroClass.toZero.{u_3} W
                    (@SubNegZeroMonoid.toNegZeroClass.{u_3} W
                      (@SubtractionMonoid.toSubNegZeroMonoid.{u_3} W
                        (@SubtractionCommMonoid.toSubtractionMonoid.{u_3} W
                          (@AddCommGroup.toDivisionAddCommMonoid.{u_3} W inst_3))))))))
    (hfile :
      @LE.le.{u_2}
        (@Submodule.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
        (@Preorder.toLE.{u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          (@PartialOrder.toPreorder.{u_2}
            (@Submodule.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
            (@Submodule.instPartialOrder.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
        file
        (@Submodule.span.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
          (@Set.range.{u_2, 1} V (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) columns))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration._proof_1)
    PUnit.unit.{1} PUnit.unit.{1}
    fun (sample : Nat → Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) =>
    ENNReal.toReal
      (@D5.S3.Resource.MinimumRetrievalTime.retrievalTime.{u_1, u_2, 0} K V
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) inst inst_1 inst_2 columns file sample)

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_three_kernel_obstruction\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_three_kernel_obstruction, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_three_kernel_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_three_kernel_obstruction, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration.{u_1,
  u_2, u_3}).actual (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration.{u_1,
  u_2, u_3}).variation.2.choose (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration.{u_1,
  u_2, u_3}).variation.1 (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration.{u_1,
  u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ThreeKernel\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena.{u_1,
    u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena.{u_1,
      u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena.{u_1,
        u_2, u_3}
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.actual)
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration.{u_1,
      u_2, u_3})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"retrieval_time_probability_bridge\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.retrieval_time_probability_bridge, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena.{u_1,
    u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.arena.{u_1,
      u_2, u_3}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.actual)
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration.{u_1,
    u_2, u_3})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.observation0.{u_1, u_2, u_3} : {K : Type u_1} →
  {V : Type u_2} →
    {alphabet : Type u_3} →
      [inst : Field.{u_1} K] →
        [inst_1 : AddCommGroup.{u_2} V] →
          [inst_2 :
              @Module.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)] →
            [Fintype.{u_3} alphabet] →
              [Nonempty.{u_3 + 1} alphabet] →
                [inst_5 : MeasurableSpace.{u_3} alphabet] →
                  [@MeasurableSingletonClass.{u_3} alphabet inst_5] →
                    (columns : alphabet → V) →
                      (file :
                          @Submodule.{u_1, u_2} K V
                            (@DivisionSemiring.toSemiring.{u_1} K
                              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2) →
                        (hfile :
                            @LE.le.{u_2}
                              (@Submodule.{u_1, u_2} K V
                                (@DivisionSemiring.toSemiring.{u_1} K
                                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                              (@Preorder.toLE.{u_2}
                                (@Submodule.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                (@PartialOrder.toPreorder.{u_2}
                                  (@Submodule.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                  (@Submodule.instPartialOrder.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
                              file
                              (@Submodule.span.{u_1, u_2} K V
                                (@DivisionSemiring.toSemiring.{u_1} K
                                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
                                (@Set.range.{u_2, u_3 + 1} V alphabet columns))) →
                          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                            _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.signature
                            PUnit.unit.{1} PUnit.unit.{1} :=
  fun {K : Type u_1} {V : Type u_2} {alphabet : Type u_3} [inst : Field.{u_1} K] [inst_1 : AddCommGroup.{u_2} V]
    [inst_2 :
      @Module.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)]
    [inst_3 : Fintype.{u_3} alphabet] [inst_4 : Nonempty.{u_3 + 1} alphabet] [inst_5 : MeasurableSpace.{u_3} alphabet]
    [@MeasurableSingletonClass.{u_3} alphabet inst_5] (columns : alphabet → V)
    (file :
      @Submodule.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
    (hfile :
      @LE.le.{u_2}
        (@Submodule.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
        (@Preorder.toLE.{u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          (@PartialOrder.toPreorder.{u_2}
            (@Submodule.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
            (@Submodule.instPartialOrder.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
        file
        (@Submodule.span.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2 (@Set.range.{u_2, u_3 + 1} V alphabet columns))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.signature
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.actual
    PUnit.unit.{1} PUnit.unit.{1}
    (@MeasureTheory.lintegral.{u_3} (Nat → alphabet)
      (@MeasurableSpace.pi.{0, u_3} Nat (fun (a : Nat) => alphabet) fun (a : Nat) => inst_5)
      (@D5.S3.Resource.MinimumRetrievalTime.uniformSamples.{u_3} alphabet inst_3 inst_4 inst_5)
      fun (sample : Nat → alphabet) =>
      @D5.S3.Resource.MinimumRetrievalTime.retrievalTime.{u_1, u_2, u_3} K V alphabet inst inst_1 inst_2 columns file
        sample)

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"retrieval_time_probability_bridge\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.retrieval_time_probability_bridge, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"retrieval_time_probability_bridge\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.retrieval_time_probability_bridge, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration.{u_1,
  u_2, u_3}).actual (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration.{u_1,
  u_2, u_3}).variation.2.choose (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration.{u_1,
  u_2, u_3}).variation.1 (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration.{u_1,
  u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"ProbabilityBridge\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ProbabilityBridge.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena.{u_1,
    u_2}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena.{u_1,
      u_2}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena.{u_1,
        u_2}
      (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration.{u_1,
      u_2})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_bad_pairs_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_bad_pairs_obstruction, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena.{u_1,
    u_2}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.arena.{u_1,
      u_2}
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
  _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration.{u_1,
    u_2})

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.observation0.{u_1, u_2} : {K : Type u_1} →
  {V : Type u_2} →
    [inst : Field.{u_1} K] →
      [inst_1 : AddCommGroup.{u_2} V] →
        [inst_2 :
            @Module.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)] →
          (columns : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → V) →
            (file :
                @Submodule.{u_1, u_2} K V
                  (@DivisionSemiring.toSemiring.{u_1} K
                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2) →
              (common left right : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
                (hcommonLeft :
                    @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) common left) →
                  (hcommonRight :
                      @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) common right) →
                    (hleftRight :
                        @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left right) →
                      (hbadLeft :
                          Not
                            (@LE.le.{u_2}
                              (@Submodule.{u_1, u_2} K V
                                (@DivisionSemiring.toSemiring.{u_1} K
                                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                              (@Preorder.toLE.{u_2}
                                (@Submodule.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                (@PartialOrder.toPreorder.{u_2}
                                  (@Submodule.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                  (@Submodule.instPartialOrder.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
                              file
                              (@Submodule.span.{u_1, u_2} K V
                                (@DivisionSemiring.toSemiring.{u_1} K
                                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
                                (@Insert.insert.{u_2, u_2} V (Set.{u_2} V) (@Set.instInsert.{u_2} V) (columns common)
                                  (@Singleton.singleton.{u_2, u_2} V (Set.{u_2} V) (@Set.instSingletonSet.{u_2} V)
                                    (columns left)))))) →
                        (hbadRight :
                            Not
                              (@LE.le.{u_2}
                                (@Submodule.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                (@Preorder.toLE.{u_2}
                                  (@Submodule.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                  (@PartialOrder.toPreorder.{u_2}
                                    (@Submodule.{u_1, u_2} K V
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                    (@Submodule.instPartialOrder.{u_1, u_2} K V
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
                                file
                                (@Submodule.span.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
                                  (@Insert.insert.{u_2, u_2} V (Set.{u_2} V) (@Set.instInsert.{u_2} V) (columns common)
                                    (@Singleton.singleton.{u_2, u_2} V (Set.{u_2} V) (@Set.instSingletonSet.{u_2} V)
                                      (columns right)))))) →
                          (hfile :
                              @LE.le.{u_2}
                                (@Submodule.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                (@Preorder.toLE.{u_2}
                                  (@Submodule.{u_1, u_2} K V
                                    (@DivisionSemiring.toSemiring.{u_1} K
                                      (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                    (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                  (@PartialOrder.toPreorder.{u_2}
                                    (@Submodule.{u_1, u_2} K V
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
                                    (@Submodule.instPartialOrder.{u_1, u_2} K V
                                      (@DivisionSemiring.toSemiring.{u_1} K
                                        (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
                                file
                                (@Submodule.span.{u_1, u_2} K V
                                  (@DivisionSemiring.toSemiring.{u_1} K
                                    (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                                  (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
                                  (@Set.range.{u_2, 1} V
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) columns))) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                              (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              PUnit.unit.{1} PUnit.unit.{1} :=
  fun {K : Type u_1} {V : Type u_2} [inst : Field.{u_1} K] [inst_1 : AddCommGroup.{u_2} V]
    [inst_2 :
      @Module.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)]
    (columns : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → V)
    (file :
      @Submodule.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
    (common left right : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (hcommonLeft : @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) common left)
    (hcommonRight : @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) common right)
    (hleftRight : @Ne.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) left right)
    (hbadLeft :
      Not
        (@LE.le.{u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          (@Preorder.toLE.{u_2}
            (@Submodule.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
            (@PartialOrder.toPreorder.{u_2}
              (@Submodule.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
              (@Submodule.instPartialOrder.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
          file
          (@Submodule.span.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
            (@Insert.insert.{u_2, u_2} V (Set.{u_2} V) (@Set.instInsert.{u_2} V) (columns common)
              (@Singleton.singleton.{u_2, u_2} V (Set.{u_2} V) (@Set.instSingletonSet.{u_2} V) (columns left))))))
    (hbadRight :
      Not
        (@LE.le.{u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          (@Preorder.toLE.{u_2}
            (@Submodule.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
            (@PartialOrder.toPreorder.{u_2}
              (@Submodule.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
              (@Submodule.instPartialOrder.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
          file
          (@Submodule.span.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
            (@Insert.insert.{u_2, u_2} V (Set.{u_2} V) (@Set.instInsert.{u_2} V) (columns common)
              (@Singleton.singleton.{u_2, u_2} V (Set.{u_2} V) (@Set.instSingletonSet.{u_2} V) (columns right))))))
    (hfile :
      @LE.le.{u_2}
        (@Submodule.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
        (@Preorder.toLE.{u_2}
          (@Submodule.{u_1, u_2} K V
            (@DivisionSemiring.toSemiring.{u_1} K
              (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
            (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
          (@PartialOrder.toPreorder.{u_2}
            (@Submodule.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
            (@Submodule.instPartialOrder.{u_1, u_2} K V
              (@DivisionSemiring.toSemiring.{u_1} K
                (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)))
        file
        (@Submodule.span.{u_1, u_2} K V
          (@DivisionSemiring.toSemiring.{u_1} K
            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2
          (@Set.range.{u_2, 1} V (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) columns))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralSignature
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (@_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.integralActual
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      _private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.ThreeKernel.registration._proof_1)
    PUnit.unit.{1} PUnit.unit.{1}
    fun (sample : Nat → Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) =>
    ENNReal.toReal
      (@D5.S3.Resource.MinimumRetrievalTime.retrievalTime.{u_1, u_2, 0} K V
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) inst inst_1 inst_2 columns file sample)

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_bad_pairs_obstruction\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_bad_pairs_obstruction, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"five_column_bad_pairs_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Resource.MinimumRetrievalTime, declaration := `D5.S3.Resource.MinimumRetrievalTime.five_column_bad_pairs_obstruction, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration.{u_1,
  u_2}).actual (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration.{u_1,
  u_2}).variation.2.choose (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration.{u_1,
  u_2}).variation.1 (_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration.{u_1,
  u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"MinimumRetrievalTime\",\"Auxiliary\",\"BadPairs\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Resource.MinimumRetrievalTime, declaration := `_private.Reg.D5.S3.Resource.MinimumRetrievalTime.0.Reg.D5.S3.Resource.MinimumRetrievalTime.Auxiliary.BadPairs.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
