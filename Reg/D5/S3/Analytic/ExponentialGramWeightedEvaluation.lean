import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExponentialGramWeightedEvaluation
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for weighted exponential evaluation. -/

noncomputable section

open ExponentialGramWeightedEvaluation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix MeasureTheory Set
open scoped BigOperators

namespace Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation

universe u

abbrev energySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def energyActual : Realization energySignature :=
  realize energySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def energyRejected : Realization energySignature :=
  realize energySignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev energyArena : Arena where
  signature := energySignature
  Law R := ∀ {ι : Type u} [Fintype ι] (h : ℝ) (ω : ι → ℝ) (_hh : 0 < h) (a : ι → ℂ),
    IntegrableOn (weightedDensity h ω a) (Ioi 0) ∧
      R.readout () () (weightedEnergy h ω a : ℂ) (star a ⬝ᵥ (gram h ω *ᵥ a))

private theorem energyRejectedLaw : ¬ energyArena.{u}.Law energyRejected := by
  intro law
  exact (law (ι := ULift.{u} (Fin 1)) 1 (fun _ => 0) zero_lt_one 0).2

private theorem energyDependence : ObservationalDependence energySignature energyActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have h := congrFun heq 0
  norm_num [energyActual, realize] at h

def energyFamily : Registration energyArena.{u} (type_of% @weightedEnergy_eq_gram.{u}) where
  actual := energyActual
  bridge := Iff.rfl
  variation := ⟨@weightedEnergy_eq_gram.{u}, energyRejected, energyRejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    energyArena.{u}.Law energyActual energyRejected energyRejectedLaw.{u}
  dependence := energyDependence

def energyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weightedEnergy_eq_gram.{u}) (Realization energySignature) Unit Unit where
  unitName := `ExponentialGramWeightedEvaluation.weightedEnergy_eq_gram.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation.energyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨energyArena.{u}⟩
  objectArena := .source ⟨energyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source energyArena.{u} ⟨energyFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize energySignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialGramWeightedEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev evaluationSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def evaluationActual : Realization evaluationSignature :=
  realize evaluationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def evaluationRejected : Realization evaluationSignature :=
  realize evaluationSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem evaluationDependence : ObservationalDependence evaluationSignature evaluationActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have h := congrFun heq 0
  norm_num [evaluationActual, realize] at h

abbrev boundArena : Arena where
  signature := evaluationSignature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (h : ℝ) (ω : ι → ℝ) (_hh : 0 < h) (_hω : Function.Injective ω),
    let b := (gram h ω)⁻¹ *ᵥ (1 : ι → ℂ)
    (∀ a : ι → ℂ, R.readout () () (‖∑ i, a i‖ ^ 2)
      ((h * (Fintype.card ι : ℝ)) * weightedEnergy h ω a)) ∧
    ‖∑ i, b i‖ ^ 2 = (h * (Fintype.card ι : ℝ)) * weightedEnergy h ω b

private theorem boundRejectedLaw : ¬ boundArena.{u}.Law evaluationRejected := by
  classical
  intro law
  exact (law (ι := ULift.{u} (Fin 1)) 1 (fun _ => 0) zero_lt_one
    (fun _ _ _ => Subsingleton.elim _ _)).1 0

def boundFamily : Registration boundArena.{u} (type_of% @weighted_evaluation.{u}) where
  actual := evaluationActual
  bridge := Iff.rfl
  variation := ⟨@weighted_evaluation.{u}, evaluationRejected, boundRejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    boundArena.{u}.Law evaluationActual evaluationRejected boundRejectedLaw.{u}
  dependence := evaluationDependence

def boundAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_evaluation.{u}) (Realization evaluationSignature) Unit Unit where
  unitName := `ExponentialGramWeightedEvaluation.weighted_evaluation.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation.boundFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena.{u}⟩
  objectArena := .source ⟨boundArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena.{u} ⟨boundFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialGramWeightedEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev leastArena : Arena where
  signature := evaluationSignature
  Law R := ∀ {ι : Type u} [Fintype ι] [Nonempty ι]
    (h : ℝ) (ω : ι → ℝ) (_hh : 0 < h) (_hω : Function.Injective ω),
    IsLeast {C : ℝ | ∀ a : ι → ℂ, R.readout () () (‖exponentialSum ω a 0‖ ^ 2)
      (C * (∫ s : ℝ in Ici 0, weightedDensity h ω a s))} (h * (Fintype.card ι : ℝ))

private theorem leastRejectedLaw : ¬ leastArena.{u}.Law evaluationRejected := by
  intro law
  exact (law (ι := ULift.{u} (Fin 1)) 1 (fun _ => 0) zero_lt_one
    (fun _ _ _ => Subsingleton.elim _ _)).1 0

def leastFamily :
    Registration leastArena.{u} (type_of% @weighted_evaluation_least_constant.{u}) where
  actual := evaluationActual
  bridge := Iff.rfl
  variation := ⟨@weighted_evaluation_least_constant.{u}, evaluationRejected, leastRejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    leastArena.{u}.Law evaluationActual evaluationRejected leastRejectedLaw.{u}
  dependence := evaluationDependence

def leastAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_evaluation_least_constant.{u}) (Realization evaluationSignature) Unit Unit where
  unitName := `ExponentialGramWeightedEvaluation.weighted_evaluation_least_constant.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation.leastFamily
  realizationSource := none
  generated := false
  arena := .source ⟨leastArena.{u}⟩
  objectArena := .source ⟨leastArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source leastArena.{u} ⟨leastFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialGramWeightedEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.ExponentialGramWeightedEvaluation
