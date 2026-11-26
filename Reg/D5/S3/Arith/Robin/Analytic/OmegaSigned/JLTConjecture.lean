import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture
import Reg.Support.SingleDependentReadout

/-! Source families for the quantitative bounds and their limiting consequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture

namespace Quantitative

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => B a) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : ℝ, 64 ≤ a →
    a / (a + 1) - R.readout false () a ≤ s a ∧
      s a ≤ 1 + R.readout true () a

def rejected (i : Bool) : Realization signature :=
  realize signature
    (fun j _ a => if j = i then
      if i then s a - 2 else a / (a + 1) - s a - 1
      else B a)
    (fun e => nomatch e)

private theorem rejected_law (i : Bool) : ¬ arena.Law (rejected i) := by
  intro h
  have hb := h 64 (by norm_num)
  cases i
  · have hl := hb.1
    change (64 : ℝ) / (64 + 1) -
      ((64 : ℝ) / (64 + 1) - s 64 - 1) ≤ s 64 at hl
    linarith only [hl]
  · have hu := hb.2
    change s 64 ≤ 1 + (s 64 - 2) at hu
    linarith only [hu]

def family : Registration arena (type_of% @quantitative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quantitative, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      funext p a
      simp only [actual, rejected, realize, if_neg hji]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 64, ?_⟩
    change B 0 ≠ B 64
    have hlog : Real.logb 2 64 = 6 := by
      calc
        Real.logb 2 64 = Real.logb 2 ((2 : ℝ) ^ (6 : ℕ)) := by norm_num
        _ = 6 * Real.logb 2 2 := Real.logb_pow 2 2 6
        _ = 6 := by
          rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
          norm_num
    norm_num [B, hlog, Real.rpow_ofNat]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quantitative) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture.quantitative.audit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture.Quantitative.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Quantitative

namespace Limit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () s atTop (𝓝 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
    intro he
    have he' := congrFun (congrFun he atTop) (𝓝 (0 : ℝ))
    have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp he' tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture.result.audit
  realizationName :=
    `Reg.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture.Limit.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture
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

end Limit

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSigned.JLTConjecture
