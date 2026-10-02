import D5.S3.Resource.MinimumRetrievalTime
import Reg.Support.CounterexampleRecord
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

namespace Reg.D5.S3.Resource.MinimumRetrievalTime

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
open _root_.D5.S3.Resource.MinimumRetrievalTime
open MeasureTheory Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def predicate (model : FiniteFieldModel) : Prop :=
  @paretoCodeLengthMonotonicity model.carrier model.field

private def embed : Fin 1 → FiniteFieldModel := fun _ => ⟨ZMod 2, inferInstance, inferInstance⟩

private def decision : ∀ witness : Fin 1, Decidable (predicate (embed witness)) :=
  fun _ => .isFalse (by
    intro h
    change paretoCodeLengthMonotonicity (ZMod 2) at h
    have hmono : paretoCodeLengthMonotonicity (ZMod 2) := h
    let basis : Module.Basis (Fin 3) (ZMod 2) (Fin 3 → ZMod 2) := Pi.basisFun _ _
    have hfirstIndices : {index : Fin (1 + 2) | index.val < 1} = {0} := by
      ext index
      fin_cases index <;> decide
    have hsecondIndices : {index : Fin (1 + 2) | 1 ≤ index.val} = {1, 2} := by
      ext index
      fin_cases index <;> decide
    have hfirst : firstCoordinateFile (ZMod 2) 1 2 = oldFirstFile basis := by
      simp only [firstCoordinateFile, hfirstIndices, Set.image_singleton]
      rfl
    have hsecond : secondCoordinateFile (ZMod 2) 1 2 = oldSecondFile basis := by
      simp only [secondCoordinateFile, hsecondIndices, Set.image_pair]
      rfl
    obtain ⟨hfull, hfirstMean, hsecondMean⟩ := old_code_actual_expectations basis
    have holdRank : Matrix.rank (Matrix.of (fun row column => oldColumns basis column row)) =
        1 + 2 := by
      rw [Matrix.rank_eq_finrank_span_cols]
      change Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range (oldColumns basis))) = _
      rw [hfull]
      simp
    obtain ⟨successor, hsuccessor, hfirstBound, hsecondBound⟩ :=
      hmono 1 2 (by decide) (by decide) (by decide) 4 (by decide) (oldColumns basis) holdRank
    have hsuccessorFull : Submodule.span (ZMod 2) (Set.range successor) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Matrix.rank_eq_finrank_span_cols] at hsuccessor
      change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range successor)) =
        1 + 2 at hsuccessor
      simpa using hsuccessor
    rw [hfirst, hfirstMean] at hfirstBound
    rw [hsecond, hsecondMean] at hsecondBound
    rcases five_column_universal_obstruction basis successor hsuccessorFull with hbad | hbad
    · exact (not_lt_of_ge hfirstBound) hbad
    · exact (not_lt_of_ge hsecondBound) hbad)

private def arena := WitnessArena.ofCarrier (Fin 1) FiniteFieldModel predicate embed decision
private def reads := arena.realization

private instance : DecidableEq arena.State := arena.stateDecidableEq

private theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
private theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads :=
  ⟨arena.law_refutes⟩
private theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue :=
  arena.variation law
private theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena :=
  arena.sensitivity law

register_information_theorem _root_.D5.S3.Resource.MinimumRetrievalTime.result in arena
  readout via (@counterexampleRealization (Fin 1) arena.check)
  primitives reads.toPrimitiveBundle realization bridge
  variation variation sensitivity sensitivity
  escape from (FiniteFieldModel) escape continues (open)

end
end Reg.D5.S3.Resource.MinimumRetrievalTime

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

register_information_theorem retrieval_time_probability_bridge in arena
  readout via (realize signature (fun _ _ value => value.toReal)
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.MinimumRetrievalTime
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

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

register_information_theorem old_code_actual_expectations in arena
  readout via (realize (integralSignature 4)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples (Fin 4))
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.MinimumRetrievalTime
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

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

register_information_theorem five_column_three_kernel_obstruction in arena
  readout via (realize (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples (Fin 5))
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.MinimumRetrievalTime
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

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

register_information_theorem five_column_bad_pairs_obstruction in arena
  readout via (realize (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples (Fin 5))
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.MinimumRetrievalTime
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

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

register_information_theorem five_column_projected_obstruction in arena
  readout via (realize (integralSignature 5)
    (fun _ _ observation => ∫ sample, observation sample ∂uniformSamples (Fin 5))
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.MinimumRetrievalTime
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

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

private def selection : SourceSelection := {
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
