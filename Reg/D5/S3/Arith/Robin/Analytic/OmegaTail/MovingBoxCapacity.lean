import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
import Reg.Support.SingleDependentReadout

/-! Source-bound observations for the finite Abel estimate and moving capacity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Real Filter MeasureTheory Set LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeInterval)
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity

namespace LocalError

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2 * |Chebyshev.theta 2 - 2| / log 2 + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {y z E : ℝ}, 2 ≤ y → y ≤ z →
    (∀ t ∈ Icc y z, |Chebyshev.theta t - t| ≤ E) →
    R.readout () () (((primeInterval y z).card : ℝ) - ∫ t in y..z, (log t)⁻¹) ≤
      2 * E / log y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbound (t : ℝ) (ht : t ∈ Icc (2 : ℝ) 2) :
      |Chebyshev.theta t - t| ≤ |Chebyshev.theta 2 - 2| := by
    have he : t = 2 := le_antisymm ht.2 ht.1
    simp [he]
  have hb := h le_rfl le_rfl hbound
  change 2 * |Chebyshev.theta 2 - 2| / log 2 + 1 ≤ 2 * |Chebyshev.theta 2 - 2| / log 2 at hb
  linarith

def family : Registration arena (type_of% @abs_primeInterval_card_sub_integral_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abs_primeInterval_card_sub_integral_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change |(0 : ℝ)| ≠ |(1 : ℝ)|
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@abs_primeInterval_card_sub_integral_le) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity.abs_primeInterval_card_sub_integral_le.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity.LocalError.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LocalError

namespace Capacity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {C a u v : ℝ}, 0 < C → 0 < a → u < v →
    R.readout () () (fun P : ℝ =>
      ((primeInterval (P * exp (u / (C * log P ^ a)))
        (P * exp (v / (C * log P ^ a)))).card : ℝ) /
          ((P / log P) / (C * log P ^ a))) atTop (𝓝 (v - u))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (C := 1) (a := 1) (u := 0) (v := 1) (by norm_num) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @primeInterval_moving_log_power_capacity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@primeInterval_moving_log_power_capacity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
    intro he
    have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@primeInterval_moving_log_power_capacity) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity.primeInterval_moving_log_power_capacity.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity.Capacity.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Capacity

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.MovingBoxCapacity
