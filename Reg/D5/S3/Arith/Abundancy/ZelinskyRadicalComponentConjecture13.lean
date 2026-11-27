import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13
import Reg.Support.SingleDependentReadout

/-! The complete negated relative-density claim with its limit-relation readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13
open _root_.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
  (count radicalComponentSet)
open _root_.D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive (PrimitiveNonDeficient)

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13

namespace Refutation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => Filter ℕ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ¬ R.readout () () (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩
        {n | PrimitiveNonDeficient n ∧ Odd n}) X : ℝ) /
        count {n | PrimitiveNonDeficient n ∧ Odd n} X) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact fun h => h trivial

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
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
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13.result.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13.Refutation.family
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
    owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13
    definition := some {
      owner := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13
      name := `D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Refutation

end Reg.D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjecture13
