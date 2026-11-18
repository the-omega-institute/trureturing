import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail

namespace FinitePower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → ∀ {N : ℕ}, 0 < N →
    ∀ S : Finset ℕ, (∀ n ∈ S, N < n) →
    R.readout () () (∑ n ∈ S, (n : ℝ) ^ (-s)) ((N : ℝ) ^ (1 - s) / (s - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (by norm_num) (N := 1) (by norm_num) ∅ (by simp)

def family : Registration arena (type_of% @finite_power_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_power_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_power_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.finite_power_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.FinitePower.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail
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

end FinitePower

namespace SmallWeight

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s : ℝ}, 2 ≤ P → 0 ≤ s →
    ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ P / 2) →
    R.readout () () (∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)))
      (P * (1 / 2 : ℝ) ^ s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 2) (s := 0) le_rfl le_rfl ∅ (by simp)

def family : Registration arena (type_of% @small_weight_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@small_weight_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@small_weight_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.small_weight_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.SmallWeight.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail
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

end SmallWeight

namespace LargeWeight

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s : ℝ}, 2 ≤ P → 2 ≤ s →
    ∀ S : Finset ℕ, (∀ n ∈ S, 2 * P < (n : ℝ)) →
    R.readout () () (∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)))
      (2 * P * (2 / 3 : ℝ) ^ s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 2) (s := 2) le_rfl le_rfl ∅ (by simp)

def family : Registration arena (type_of% @large_weight_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@large_weight_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@large_weight_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.large_weight_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.LargeWeight.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail
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

end LargeWeight

namespace GeometricDecay

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {c q : ℝ}, 0 < c → 0 < q → q < 1 →
    R.readout () () (fun t : ℝ => t * sqrt t * q ^ (c * sqrt t)) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 1) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @geometric_sqrt_decay) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@geometric_sqrt_decay, rejected, rejected_law⟩
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
    (@geometric_sqrt_decay) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.geometric_sqrt_decay.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail.GeometricDecay.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeometricDecay

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Tail
