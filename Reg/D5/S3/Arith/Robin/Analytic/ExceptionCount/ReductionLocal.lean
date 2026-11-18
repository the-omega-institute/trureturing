import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Real LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal

namespace Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal

namespace LocalFactor

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ r a : ℝ}, 1 ≤ κ → 0 ≤ r → r ≤ 1 / 2 → 1 ≤ a →
    R.readout () () (normalizedLocalFactor κ r a) ((1-r)^(-κ)*(1-r^κ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (κ := 1) (r := 0) (a := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

def family : Registration arena (type_of% @local_factor_upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_factor_upper_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@local_factor_upper_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal.local_factor_upper_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal.LocalFactor.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LocalFactor

namespace Endpoint

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f S => MonotoneOn f S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {κ : ℝ}, 1 ≤ κ →
    R.readout () () (fun r : ℝ => (1-r)^(-κ)*(1-r^κ)) (Ico 0 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (κ := 1) (by norm_num)

def family : Registration arena (type_of% @endpoint_monotone) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endpoint_monotone, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun x : ℝ => x), (fun x : ℝ => -x), ?_⟩
    intro he
    have hid : MonotoneOn (fun x : ℝ => x) (Ico 0 1) :=
      fun _ _ _ _ h => h
    have hEq := congrFun he (Ico (0 : ℝ) 1)
    change MonotoneOn (fun x : ℝ => x) (Ico 0 1) =
      MonotoneOn (fun x : ℝ => -x) (Ico 0 1) at hEq
    have hneg : MonotoneOn (fun x : ℝ => -x) (Ico 0 1) := Eq.mp hEq hid
    have hh := hneg (a := 0) (by simp) (b := 1 / 2) (by norm_num) (by norm_num)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_monotone) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal.endpoint_monotone.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal.Endpoint.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

namespace Support

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S T : Finset ℕ} {f : ℕ → ℝ} {B : ℝ},
    S.card ≤ T.card → 1 ≤ B → (∀ p ∈ S, 0 ≤ f p) →
    (∀ p ∈ S \ T, f p ≤ B) → (∀ p ∈ T \ S, B ≤ f p) →
    R.readout () () (∏ p ∈ S, f p) (∏ p ∈ T, f p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (S := ∅) (T := ∅) (f := fun _ => 1) (B := 1)
    (by simp) le_rfl (by simp) (by simp) (by simp)

def family : Registration arena (type_of% @support_product_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@support_product_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@support_product_le) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal.support_product_le.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal.Support.family
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
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

end Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
