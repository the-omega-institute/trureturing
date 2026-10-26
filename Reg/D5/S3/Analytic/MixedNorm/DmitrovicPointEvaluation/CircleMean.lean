import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! Typed source observations for power-family means and evaluation inequalities. -/

open _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
open _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Defs
open _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped ENNReal
noncomputable section
namespace Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean

abbrev normSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => ℂ) (fun _ => ℝ)

def normActual : Realization normSignature :=
  realize normSignature (fun _ v x => ‖x‖) (fun e => nomatch e)

def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ x => 0) (fun e => nomatch e)

private theorem norm_dependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [normActual, realize]

abbrev ofRealSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => ℝ) (fun _ => ℝ≥0∞)

def ofRealActual : Realization ofRealSignature :=
  realize ofRealSignature (fun _ v x => ENNReal.ofReal x) (fun e => nomatch e)

def ofRealRejected : Realization ofRealSignature :=
  realize ofRealSignature (fun _ _ x => ∞) (fun e => nomatch e)

private theorem ofReal_dependence : ObservationalDependence ofRealSignature ofRealActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [ofRealActual, realize]

abbrev circleSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ≥0∞)

def circleActual : Realization circleSignature :=
  realize circleSignature (fun _ v x => circleMean (ENNReal.ofReal v.1) (powerFamily v.1 v.2) x) (fun e => nomatch e)

def circleRejected : Realization circleSignature :=
  realize circleSignature (fun _ _ x => 0) (fun e => nomatch e)

private theorem circle_dependence : ObservationalDependence circleSignature circleActual := by
  intro i
  refine ⟨⟨1, 1/2⟩, 0, 1/2, ?_⟩
  change circleMean (ENNReal.ofReal 1) (powerFamily 1 (1/2)) 0 ≠
    circleMean (ENNReal.ofReal 1) (powerFamily 1 (1/2)) (1/2)
  rw [circleMean_powerFamily (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num),
    circleMean_powerFamily (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
  intro hh
  have ht := congrArg ENNReal.toReal hh
  norm_num at ht

abbrev finiteSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℂ → ℂ) (fun _ => ℝ≥0∞)

def finiteActual : Realization finiteSignature :=
  realize finiteSignature (fun _ v x => mixedNorm (ENNReal.ofReal v.1) (ENNReal.ofReal v.2.1) v.2.2 x) (fun e => nomatch e)

def finiteRejected : Realization finiteSignature :=
  realize finiteSignature (fun _ _ x => ∞) (fun e => nomatch e)

private theorem finite_dependence : ObservationalDependence finiteSignature finiteActual := by
  intro i
  refine ⟨⟨1, 1, 1⟩, (fun _ => 0), powerFamily 1 0, ?_⟩
  change mixedNorm (ENNReal.ofReal 1) (ENNReal.ofReal 1) 1 (fun _ => 0) ≠
    mixedNorm (ENNReal.ofReal 1) (ENNReal.ofReal 1) 1 (powerFamily 1 0)
  rw [mixedNorm_powerFamily_finite (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num [mixedNorm, circleMean, radialIntegral, integral_id]

abbrev infinitySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℂ → ℂ) (fun _ => ℝ≥0∞)

def infinityActual : Realization infinitySignature :=
  realize infinitySignature (fun _ v x => mixedNorm (ENNReal.ofReal v.1) ∞ v.2 x) (fun e => nomatch e)

def infinityRejected : Realization infinitySignature :=
  realize infinitySignature (fun _ _ x => 0) (fun e => nomatch e)

private theorem infinity_dependence : ObservationalDependence infinitySignature infinityActual := by
  intro i
  refine ⟨⟨1, 1⟩, (fun _ => 0), powerFamily 1 0, ?_⟩
  change mixedNorm (ENNReal.ofReal 1) ∞ 1 (fun _ => 0) ≠
    mixedNorm (ENNReal.ofReal 1) ∞ 1 (powerFamily 1 0)
  rw [mixedNorm_powerFamily_infinity (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num [mixedNorm, circleMean]

abbrev holomorphicSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℂ) (fun _ => ℂ)

def holomorphicActual : Realization holomorphicSignature :=
  realize holomorphicSignature (fun _ v x => powerFamily v.1 v.2 x) (fun e => nomatch e)

def holomorphicRejected : Realization holomorphicSignature :=
  realize holomorphicSignature (fun _ _ x => (‖x‖ : ℂ)) (fun e => nomatch e)

private theorem holomorphic_dependence : ObservationalDependence holomorphicSignature holomorphicActual := by
  intro i
  refine ⟨⟨2, 1/2⟩, 0, 1, ?_⟩
  norm_num [holomorphicActual, realize, powerFamily, Complex.exp_log]

def zeroOfReal : Realization ofRealSignature :=
  realize ofRealSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev normArena : Arena where
  signature := normSignature
  Law R := ∀ {p a : ℝ}, 0 < p → 0 ≤ a → a < 1 → ∀ {w : ℂ}, ‖w‖ < 1 →
    R.readout () () (powerFamily p a w) = ‖1 + (a : ℂ) * w‖ ^ (2 / p)

private theorem norm_rejected : ¬ normArena.Law normRejected := by
  intro h
  have hh := h (p := 2) (a := 0) (by norm_num) (by norm_num) (by norm_num)
    (w := 0) (by norm_num)
  norm_num [normRejected, realize] at hh

def normEvidence : Registration normArena (type_of% @norm_powerFamily) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@norm_powerFamily, normRejected, norm_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    normArena.Law normActual normRejected norm_rejected
  dependence := norm_dependence

def normAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_powerFamily) (Realization normSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.normUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.normEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨normArena⟩
  objectArena := .source ⟨normArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normArena ⟨normEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature
    (fun _ v x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev circleArena : Arena where
  signature := circleSignature
  Law R := ∀ {p a ρ : ℝ}, 0 < p → 0 ≤ a → a < 1 → 0 ≤ ρ → ρ < 1 →
    R.readout () ⟨p,a⟩ ρ = ENNReal.ofReal ((1 + a ^ 2 * ρ ^ 2) ^ (1 / p))

private theorem circle_rejected : ¬ circleArena.Law circleRejected := by
  intro h
  have hh := h (p := 1) (a := 0) (ρ := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [circleRejected, realize] at hh

def circleEvidence : Registration circleArena (type_of% @circleMean_powerFamily) where
  actual := circleActual
  bridge := Iff.rfl
  variation := ⟨@circleMean_powerFamily, circleRejected, circle_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    circleArena.Law circleActual circleRejected circle_rejected
  dependence := circle_dependence

def circleAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@circleMean_powerFamily) (Realization circleSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.circleUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.circleEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨circleArena⟩
  objectArena := .source ⟨circleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source circleArena ⟨circleEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize circleSignature
    (fun _ v x => circleMean (ENNReal.ofReal v.1) (powerFamily v.1 v.2) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev finiteArena : Arena where
  signature := ofRealSignature
  Law R := ∀ {p q α a : ℝ}, 0 < p → 0 < q → 0 < α → 0 ≤ a → a < 1 →
    mixedNorm (ENNReal.ofReal p) (ENNReal.ofReal q) α (powerFamily p a) =
      R.readout () () ((radialIntegral p q α (a ^ 2)) ^ (1 / q))

private theorem finite_rejected : ¬ finiteArena.Law ofRealRejected := by
  intro h
  have hh := h (p := 1) (q := 1) (α := 1) (a := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hf := mixedNorm_powerFamily_lt_top (p := 1) (q := 1) (α := 1) (a := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hh] at hf
  exact (lt_irrefl (∞ : ℝ≥0∞)) hf

def finiteEvidence : Registration finiteArena (type_of% @mixedNorm_powerFamily_finite) where
  actual := ofRealActual
  bridge := Iff.rfl
  variation := ⟨@mixedNorm_powerFamily_finite, ofRealRejected, finite_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    finiteArena.Law ofRealActual ofRealRejected finite_rejected
  dependence := ofReal_dependence

def finiteAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixedNorm_powerFamily_finite) (Realization ofRealSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.finiteUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.finiteEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ofRealSignature
    (fun _ v x => ENNReal.ofReal x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev finiteBoundArena : Arena where
  signature := finiteSignature
  Law R := ∀ {p q α a : ℝ}, 0 < p → 0 < q → 0 < α → 0 ≤ a → a < 1 →
    R.readout () ⟨p,q,α⟩ (powerFamily p a) < ∞

private theorem finiteBound_rejected : ¬ finiteBoundArena.Law finiteRejected := by
  intro h
  have hh := h (p := 1) (q := 1) (α := 1) (a := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (∞ : ℝ≥0∞)) hh

def finiteBoundEvidence : Registration finiteBoundArena (type_of% @mixedNorm_powerFamily_lt_top) where
  actual := finiteActual
  bridge := Iff.rfl
  variation := ⟨@mixedNorm_powerFamily_lt_top, finiteRejected, finiteBound_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    finiteBoundArena.Law finiteActual finiteRejected finiteBound_rejected
  dependence := finite_dependence

def finiteBoundAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixedNorm_powerFamily_lt_top) (Realization finiteSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.finiteBoundUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.finiteBoundEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨finiteBoundArena⟩
  objectArena := .source ⟨finiteBoundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteBoundArena ⟨finiteBoundEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteSignature
    (fun _ v x => mixedNorm (ENNReal.ofReal v.1) (ENNReal.ofReal v.2.1) v.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev evaluationArena : Arena where
  signature := normSignature
  Law R := ∀ {p q α a : ℝ}, 0 < p → 0 < α → 0 ≤ a → a < 1 →
    let c := 1 / (1 + α * p)
    (R.readout () () (powerFamily p a ((c * a : ℝ) : ℂ))) ^ q *
      (1 - (c * a) ^ 2) ^ (q * (α + 1 / p)) = evaluationExcess p q α (a ^ 2)

private theorem evaluation_rejected : ¬ evaluationArena.Law normRejected := by
  intro h
  have hh := h (p := 1) (q := 1) (α := 1) (a := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num [normRejected, realize, evaluationExcess] at hh

def evaluationEvidence : Registration evaluationArena (type_of% @evaluation_powerFamily) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@evaluation_powerFamily, normRejected, evaluation_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    evaluationArena.Law normActual normRejected evaluation_rejected
  dependence := norm_dependence

def evaluationAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@evaluation_powerFamily) (Realization normSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.evaluationUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.evaluationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨evaluationArena⟩
  objectArena := .source ⟨evaluationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evaluationArena ⟨evaluationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature
    (fun _ v x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev infinityArena : Arena where
  signature := infinitySignature
  Law R := ∀ {p α a : ℝ}, 0 < p → 0 < α → 0 ≤ a → a < 1 → a ^ 2 ≤ α * p →
    R.readout () ⟨p,α⟩ (powerFamily p a) = 1

private theorem infinity_rejected : ¬ infinityArena.Law infinityRejected := by
  intro h
  have hh := h (p := 1) (α := 1) (a := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [infinityRejected, realize] at hh

def infinityEvidence : Registration infinityArena (type_of% @mixedNorm_powerFamily_infinity) where
  actual := infinityActual
  bridge := Iff.rfl
  variation := ⟨@mixedNorm_powerFamily_infinity, infinityRejected, infinity_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    infinityArena.Law infinityActual infinityRejected infinity_rejected
  dependence := infinity_dependence

def infinityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixedNorm_powerFamily_infinity) (Realization infinitySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.infinityUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.infinityEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨infinityArena⟩
  objectArena := .source ⟨infinityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source infinityArena ⟨infinityEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize infinitySignature
    (fun _ v x => mixedNorm (ENNReal.ofReal v.1) ∞ v.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev holomorphicArena : Arena where
  signature := holomorphicSignature
  Law R := ∀ {p a : ℝ}, 0 < p → 0 ≤ a → a < 1 →
    DifferentiableOn ℂ (R.readout () ⟨p,a⟩) (Metric.ball 0 1)

private theorem holomorphic_rejected : ¬ holomorphicArena.Law holomorphicRejected := by
  intro h
  have hh := h (p := 1) (a := 0) (by norm_num) (by norm_num) (by norm_num)
  have hd : DifferentiableAt ℂ (fun w : ℂ => (‖w‖ : ℂ)) 0 :=
    hh.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))
  have hr : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) 0 := by
    have hcomp := Complex.reCLM.differentiableAt.comp 0 (hd.restrictScalars ℝ)
    change DifferentiableAt ℝ (fun w : ℂ => (Complex.ofReal ‖w‖).re) 0 at hcomp
    simpa only [Complex.ofReal_re] using hcomp
  exact not_differentiableAt_norm_zero ℂ hr

def holomorphicEvidence : Registration holomorphicArena (type_of% @powerFamily_differentiableOn) where
  actual := holomorphicActual
  bridge := Iff.rfl
  variation := ⟨@powerFamily_differentiableOn, holomorphicRejected, holomorphic_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    holomorphicArena.Law holomorphicActual holomorphicRejected holomorphic_rejected
  dependence := holomorphic_dependence

def holomorphicAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@powerFamily_differentiableOn) (Realization holomorphicSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.holomorphicUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.holomorphicEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨holomorphicArena⟩
  objectArena := .source ⟨holomorphicArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source holomorphicArena ⟨holomorphicEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize holomorphicSignature
    (fun _ v x => powerFamily v.1 v.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev infinityRefutationArena : Arena where
  signature := ofRealSignature
  Law R := ∀ {p α : ℝ}, 0 < p → 0 < α →
    ∃ a : ℝ, a ∈ Ioo (0 : ℝ) 1 ∧ ∃ z : ℂ, ‖z‖ < 1 ∧
      mixedNorm (ENNReal.ofReal p) ∞ α (powerFamily p a) < ∞ ∧
      mixedNorm (ENNReal.ofReal p) ∞ α (powerFamily p a) <
        R.readout () () ‖powerFamily p a z‖ *
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (α + 1 / (ENNReal.ofReal p).toReal)) ∧
    (∀ w : ℂ, ‖w‖ < 1 → ‖powerFamily p a w‖ ≤ (1 + a) ^ (2 / p))

private theorem infinityRefutation_rejected : ¬ infinityRefutationArena.Law zeroOfReal := by
  intro h
  obtain ⟨a, ha, z, hz, hfin, hs, hb⟩ := h (p := 1) (α := 1) (by norm_num) (by norm_num)
  have hh : mixedNorm (ENNReal.ofReal 1) ∞ 1 (powerFamily 1 a) < 0 := by
    simpa only [zeroOfReal, realize, zero_mul] using hs
  exact (not_lt_of_ge bot_le) hh

def infinityRefutationEvidence : Registration infinityRefutationArena (type_of% @refutes_at_infinity) where
  actual := ofRealActual
  bridge := Iff.rfl
  variation := ⟨@refutes_at_infinity, zeroOfReal, infinityRefutation_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    infinityRefutationArena.Law ofRealActual zeroOfReal infinityRefutation_rejected
  dependence := ofReal_dependence

def infinityRefutationAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@refutes_at_infinity) (Realization ofRealSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.infinityRefutationUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.infinityRefutationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨infinityRefutationArena⟩
  objectArena := .source ⟨infinityRefutationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source infinityRefutationArena ⟨infinityRefutationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ofRealSignature
    (fun _ v x => ENNReal.ofReal x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev gapArena : Arena where
  signature := ofRealSignature
  Law R := ∀ {p q α a : ℝ}, 0 < p → 0 < q → 0 < α → 0 < a → a < 1 →
    radialIntegral p q α (a ^ 2) < evaluationExcess p q α (a ^ 2) →
    let z : ℂ := ((1 / (1 + α * p) * a : ℝ) : ℂ)
    DifferentiableOn ℂ (powerFamily p a) (Metric.ball 0 1) ∧
    mixedNorm (ENNReal.ofReal p) (ENNReal.ofReal q) α (powerFamily p a) < ∞ ∧
    ‖z‖ < 1 ∧
    mixedNorm (ENNReal.ofReal p) (ENNReal.ofReal q) α (powerFamily p a) <
      R.readout () () ‖powerFamily p a z‖ *
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (α + 1 / (ENNReal.ofReal p).toReal)) ∧
    (∀ w : ℂ, ‖w‖ < 1 → ‖powerFamily p a w‖ ≤ (1 + a) ^ (2 / p))

private theorem gap_rejected : ¬ gapArena.Law zeroOfReal := by
  intro h
  obtain ⟨t, ht0, ht1, htgap⟩ :=
    _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap.exists_gap
      (p := 1) (q := 2) (α := 1) (by norm_num) (by norm_num) (by norm_num)
  have ha0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have ha1 : Real.sqrt t < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by simpa using ht1)
  rw [← Real.sq_sqrt ht0.le] at htgap
  have hh := h (p := 1) (q := 2) (α := 1) (a := Real.sqrt t)
    (by norm_num) (by norm_num) (by norm_num) ha0 ha1 htgap
  have hs : mixedNorm (ENNReal.ofReal 1) (ENNReal.ofReal 2) 1
      (powerFamily 1 (Real.sqrt t)) < 0 := by
    simpa only [zeroOfReal, realize, zero_mul] using hh.2.2.2.1
  exact (not_lt_of_ge bot_le) hs

def gapEvidence : Registration gapArena (type_of% @refutes_of_gap) where
  actual := ofRealActual
  bridge := Iff.rfl
  variation := ⟨@refutes_of_gap, zeroOfReal, gap_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    gapArena.Law ofRealActual zeroOfReal gap_rejected
  dependence := ofReal_dependence

def gapAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@refutes_of_gap) (Realization ofRealSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.gapUnit
  realizationName := `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean.gapEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gapArena⟩
  objectArena := .source ⟨gapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gapArena ⟨gapEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ofRealSignature
    (fun _ v x => ENNReal.ofReal x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
