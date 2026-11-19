import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
import Reg.Support.SingleDependentReadout

/-! A source family for the limit of the primitive non-deficient counting ratio. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
  (count radicalComponentSet radicalComponentCount)
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures

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
  Law R := R.readout () () (fun n => (primitiveCount n : ℝ) / n) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena
    (type_of% @primitive_density_zero) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@primitive_density_zero,
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
    (@primitive_density_zero)
    (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.primitive_density_zero.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.Limit.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
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

namespace Conjectures

abbrev signature : Signature := Limit.signature

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n}) X : ℝ) /
        radicalComponentCount 2 X) atTop (𝓝 0) ∧
    R.readout () () (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n ∧ Odd n}) X : ℝ) /
        radicalComponentCount 2 X) atTop (𝓝 0) ∧
    ∀ M : Finset ℕ, M.Nonempty → (∀ p ∈ M, p.Prime) →
      R.readout () () (fun X : ℕ =>
        (count (radicalComponentSet 2 ∩
          {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n}) X : ℝ) /
            radicalComponentCount 2 X) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h.1

def family : Registration arena (type_of% @conjectures) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conjectures, rejected, rejected_law⟩
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
    (@conjectures) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.conjectures.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures.Conjectures.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }, {
      path := #["arg", "arg", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Conjectures

end Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures
