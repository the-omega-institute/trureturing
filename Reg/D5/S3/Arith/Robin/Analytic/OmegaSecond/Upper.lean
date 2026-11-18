import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper

namespace RankinReduction

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x s : ℝ}, exp 1 < x → 2 ≤ s →
    R.readout () () (tailCount 1 x : ℝ)
      (exp (s * budget (log x) + remainder (log x) s x + eulerCost))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (x := exp 2) (s := 2) (exp_lt_exp.mpr (by norm_num)) le_rfl

def family : Registration arena (type_of% @rankin_reduction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rankin_reduction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rankin_reduction) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.rankin_reduction.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.RankinReduction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
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

end RankinReduction

namespace SecondScaleTop

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () secondScale atTop atTop

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @secondScale_top) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@secondScale_top, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩
    intro he
    have hEq := congrFun (congrFun he atTop) atTop
    change Tendsto (fun x : ℝ => x) atTop atTop =
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq
    have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
    have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId
    exact not_tendsto_const_atTop (0 : ℝ) atTop hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@secondScale_top) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.secondScale_top.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.SecondScaleTop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SecondScaleTop

namespace SaddleBudgetLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (fun P : ℝ => saddle P * budget P / (P / (log P * sqrt (log P)))) atTop (𝓝 (π / sqrt 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @saddle_budget_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@saddle_budget_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩
    intro he
    have hEq := congrFun (congrFun he atTop) atTop
    change Tendsto (fun x : ℝ => x) atTop atTop =
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq
    have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
    have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId
    exact not_tendsto_const_atTop (0 : ℝ) atTop hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@saddle_budget_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.saddle_budget_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.SaddleBudgetLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SaddleBudgetLimit

namespace Result

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    R.readout () () (tailCount 1 x : ℝ)
      (exp ((2 * π / sqrt 3 + ε) * log x / (log (log x)) ^ (3 / 2 : ℝ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := (h 1 (by norm_num)).exists
  exact hx

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.result.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper.Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Result

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
