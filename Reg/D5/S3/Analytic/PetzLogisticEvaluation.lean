import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PetzLogisticEvaluation
import Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for exact logistic factorization and sharp evaluation. -/

set_option autoImplicit false

noncomputable section

universe u

open LeanInformationAudit MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PetzLogisticEvaluation (correlation exact_gram_factorization card_le_of_uniform_bound)
open _root_.PetzExponentialBoundaryEvaluation (petzWeight distinctFrequencies)
open _root_.ExponentialGramWeightedEvaluation (exponentialSum frequency)
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped ComplexOrder MatrixOrder

open private integral_petzWeight from D5.S3.Analytic.PetzStripFiniteSeries
open private evaluationDependence from Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation

namespace Reg.D5.S3.Analytic.PetzLogisticEvaluation

namespace Factorization

private abbrev scalarSignature : Signature := signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x y => x = -y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarSignature
  Law R := ∀ {ι : Type u} [Finite ι] (ω : ι → ℝ),
    (correlation ω).PosSemidef ∧ (∀ i, correlation ω i i = 1) ∧
    ∀ i j, R.readout () () (∫ t : ℝ, (petzWeight t : ℂ) *
      Complex.exp ((((ω j - ω i) * t : ℝ) : ℂ) * Complex.I))
      (‖correlation ω i j‖ ^ 2 : ℂ)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let ω : ULift.{u} Unit → ℝ := fun _ => 0
  let i : ULift.{u} Unit := ⟨()⟩
  obtain ⟨_, diag, entry⟩ := exact_gram_factorization ω
  have bad := (law ω).2.2 i i
  change (∫ t : ℝ, (petzWeight t : ℂ) *
    Complex.exp ((((ω i - ω i) * t : ℝ) : ℂ) * Complex.I)) =
    -(‖correlation ω i i‖ ^ 2 : ℂ) at bad
  rw [entry i i, diag i] at bad
  norm_num at bad

def family : Registration arena.{u} (type_of% @exact_gram_factorization.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exact_gram_factorization.{u}, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro same
    have h := congrFun same 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_gram_factorization.{u}) (Realization scalarSignature) Unit Unit where
  unitName := `PetzLogisticEvaluation.exact_gram_factorization.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzLogisticEvaluation.Factorization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzLogisticEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Factorization

open _root_.Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation
  (evaluationSignature evaluationActual)

namespace Evaluation

def rejected : Realization evaluationSignature :=
  realize evaluationSignature (fun _ _ x y => x ≤ y / 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := evaluationSignature
  Law R := ∀ {ι : Type u} [Fintype ι] (ω : ι → ℝ) (a : ι → ℂ),
    Integrable (fun t : ℝ => petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) ∧
    R.readout () () (‖exponentialSum ω a 0‖ ^ 2) (((distinctFrequencies ω).card : ℝ) *
      (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2))

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let ω : ULift.{u} Unit → ℝ := fun _ => 0
  let a : ULift.{u} Unit → ℂ := fun _ => 1
  have hω : Function.Injective ω := fun _ _ _ => Subsingleton.elim _ _
  have hcard : (distinctFrequencies ω).card = 1 := by
    rw [distinctFrequencies, Finset.card_image_of_injective _ hω, Finset.card_univ]
    simp
  have hsum (z : ℂ) : exponentialSum ω a z = 1 := by
    simp [exponentialSum, frequency, ω, a]
  have bad := (law ω a).2
  change ‖exponentialSum ω a 0‖ ^ 2 ≤ (((distinctFrequencies ω).card : ℝ) *
    (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2)) / 2 at bad
  simp only [hcard, Nat.cast_one, hsum, norm_one, one_pow, mul_one,
    integral_petzWeight] at bad
  norm_num at bad

def family :
    Registration arena.{u} (type_of% @_root_.PetzLogisticEvaluation.weighted_evaluation.{u}) where
  actual := evaluationActual
  bridge := Iff.rfl
  variation := ⟨@_root_.PetzLogisticEvaluation.weighted_evaluation.{u}, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law evaluationActual rejected rejectedLaw
  dependence := evaluationDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.PetzLogisticEvaluation.weighted_evaluation.{u})
    (Realization evaluationSignature) Unit Unit where
  unitName := `PetzLogisticEvaluation.weighted_evaluation.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzLogisticEvaluation.Evaluation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzLogisticEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Evaluation

namespace UniformSharpness

def rejected : Realization evaluationSignature :=
  realize evaluationSignature (fun _ _ x y => x + 1 ≤ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := evaluationSignature
  Law R := ∀ {m : ℕ} (_hm : 0 < m) (K : ℝ)
    (_hK : ∀ (ω : Fin m → ℝ), Function.Injective ω → ∀ a : Fin m → ℂ,
      ‖exponentialSum ω a 0‖ ^ 2 ≤ K *
        (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2)),
    R.readout () () (m : ℝ) K

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro law
  have hK (ω : Fin 1 → ℝ) (hω : Function.Injective ω) (a : Fin 1 → ℂ) :
      ‖exponentialSum ω a 0‖ ^ 2 ≤ 1 *
        (∫ t : ℝ, petzWeight t * ‖exponentialSum ω a (t : ℂ)‖ ^ 2) := by
    have hcard : (distinctFrequencies ω).card = 1 := by
      rw [distinctFrequencies, Finset.card_image_of_injective _ hω, Finset.card_univ,
        Fintype.card_fin]
    simpa only [hcard, Nat.cast_one] using (_root_.PetzLogisticEvaluation.weighted_evaluation ω a).2
  have bad := law (m := 1) (by decide) 1 hK
  change ((1 : ℕ) : ℝ) + 1 ≤ 1 at bad
  norm_num at bad

def family : Registration arena (type_of% @card_le_of_uniform_bound) where
  actual := evaluationActual
  bridge := Iff.rfl
  variation := ⟨@card_le_of_uniform_bound, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law evaluationActual rejected rejectedLaw
  dependence := evaluationDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@card_le_of_uniform_bound) (Realization evaluationSignature) Unit Unit where
  unitName := `PetzLogisticEvaluation.card_le_of_uniform_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzLogisticEvaluation.UniformSharpness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzLogisticEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UniformSharpness

end Reg.D5.S3.Analytic.PetzLogisticEvaluation
