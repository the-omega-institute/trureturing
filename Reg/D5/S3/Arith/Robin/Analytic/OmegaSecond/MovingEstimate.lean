import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate

namespace RemainderMajorant

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, π ≤ s → 2 ≤ s → ∀ x : ℝ,
    R.readout () () (remainder P s x) (majorant P s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, hP⟩ := h.exists
  exact hP (π + 2) (by linarith) (by linarith [pi_pos]) 0

def family : Registration arena (type_of% @remainder_le_majorant) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@remainder_le_majorant, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@remainder_le_majorant) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate.remainder_le_majorant.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate.RemainderMajorant.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RemainderMajorant

namespace MajorantLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {c : ℝ}, 0 < c →
    R.readout () () (fun P : ℝ => majorant P (c * sqrt (log P)) /
      (P / (log P * sqrt (log P)))) atTop (𝓝 (π ^ 2 / (6 * c)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 1) (by norm_num)

def family : Registration arena (type_of% @majorant_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@majorant_limit, rejected, rejected_law⟩
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
    (@majorant_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate.majorant_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate.MajorantLimit.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MajorantLimit

namespace MovingUpper

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {c ε : ℝ}, 0 < c → 0 < ε → ∀ᶠ P : ℝ in atTop, ∀ x : ℝ,
    R.readout () () (remainder P (c * sqrt (log P)) x)
      ((π ^ 2 / (6 * c) + ε) * (P / (log P * sqrt (log P))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, hP⟩ := (h (c := 1) (ε := 1) (by norm_num) (by norm_num)).exists
  exact hP 0

def family : Registration arena (type_of% @moving_weight_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moving_weight_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moving_weight_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate.moving_weight_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate.MovingUpper.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MovingUpper

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate
