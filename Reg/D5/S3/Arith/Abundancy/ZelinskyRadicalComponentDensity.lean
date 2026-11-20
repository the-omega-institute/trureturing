import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
import Reg.Support.SingleDependentReadout

/-! The positive-parameter family of radical-component counting limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity

namespace Limit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => Filter ℕ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ lam : ℝ, 0 < lam →
    R.readout () () (fun X : ℕ => (radicalComponentCount lam X : ℝ) / X)
      atTop (𝓝 (1 - log 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by norm_num)

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℕ => 0), (fun _ : ℕ => 1), ?_⟩
    intro he
    have he' := congrFun (congrFun he atTop) (𝓝 (0 : ℝ))
    have hh : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp he' tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.result.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity.Limit.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
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

end Limit

end Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
