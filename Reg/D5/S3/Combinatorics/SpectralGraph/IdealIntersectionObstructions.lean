import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
import Reg.Support.SingleDependentReadout

/-! The original finite nonnegative-product law and its ordered relation readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open LeanInformationAudit Finset
open _root_.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

namespace P

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (s : Finset ι) (x : ι → ℝ), (∀ i ∈ s, 0 ≤ x i) →
    R.readout () () ((1 - ∑ i ∈ s, x i) * (∏ i ∈ s, (1 + x i))) 1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} Unit) ∅ (fun _ => 0) (by simp)

def family : Registration arena.{u}
    (type_of% @one_sub_sum_mul_prod_le_one.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_sub_sum_mul_prod_le_one.{u}, rejected, rejected_law.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law.{u}
  dependence := by
    intro role
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh := congrFun he (0 : ℝ)
    change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
    have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
    norm_num at hbad

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@one_sub_sum_mul_prod_le_one.{u})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions.P.audit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions.P.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end P

end Reg.D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
