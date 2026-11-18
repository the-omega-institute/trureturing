import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Set Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight

namespace WeightNonneg

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ P s t : ℝ, R.readout () () 0 (weight P s t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% @weight_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_nonneg) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.weight_nonneg.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.WeightNonneg.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end WeightNonneg



namespace WeightContinuity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => ContinuousOn f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s a b : ℝ}, 0 < P → 0 < a →
    R.readout () () (weight P s) (Set.Icc a b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (a := 1) (b := 2) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @weight_continuousOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weight_continuousOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), Real.log, ?_⟩
    intro he
    have hc : ContinuousOn Real.log Set.univ :=
      Eq.mp (congrFun he Set.univ) continuousOn_const
    have hc0 : ContinuousAt Real.log (0 : ℝ) := (continuousOn_univ.mp hc).continuousAt
    exact (Real.continuousAt_log_iff.mp hc0) rfl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_continuousOn) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.weight_continuousOn.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.WeightContinuity.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
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

end WeightContinuity

namespace LeftEquals

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t → 0 ≤ s → t ≤ P →
    R.readout () () (leftWeight P s t) (weight P s t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num) le_rfl le_rfl

def family : Registration arena (type_of% @leftWeight_eq_weight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@leftWeight_eq_weight, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@leftWeight_eq_weight) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.leftWeight_eq_weight.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.LeftEquals.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
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

end LeftEquals

namespace RightEquals

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t → 0 ≤ s → P ≤ t →
    R.readout () () (logWeight s (P ^ s) t) (weight P s t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num) le_rfl le_rfl

def family : Registration arena (type_of% @rightWeight_eq_weight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rightWeight_eq_weight, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rightWeight_eq_weight) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.rightWeight_eq_weight.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.RightEquals.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
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

end RightEquals

namespace LeftWeightDerivative

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => ℝ → ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t →
    R.readout () () (leftWeight P s) (s / t - abelKernel s (P ^ s) t) t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @leftWeight_deriv) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@leftWeight_deriv, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), (fun x : ℝ => x), ?_⟩
    intro he
    have hh : HasDerivAt (fun x : ℝ => x) 0 0 :=
      Eq.mp (congrFun (congrFun he 0) 0) (hasDerivAt_const 0 (0 : ℝ))
    have hzero : (1 : ℝ) = 0 := (hasDerivAt_id 0).unique hh
    norm_num at hzero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@leftWeight_deriv) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.leftWeight_deriv.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.LeftWeightDerivative.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
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


end LeftWeightDerivative

namespace LeftCutoff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s : ℝ}, 0 < P → R.readout () () (leftWeight P s P) (log 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (by norm_num)

def family : Registration arena (type_of% @leftWeight_at_cutoff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@leftWeight_at_cutoff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@leftWeight_at_cutoff) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.leftWeight_at_cutoff.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.LeftCutoff.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LeftCutoff

namespace RightCutoff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s : ℝ}, 0 < P → R.readout () () (logWeight s (P ^ s) P) (log 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (by norm_num)

def family : Registration arena (type_of% @rightWeight_at_cutoff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rightWeight_at_cutoff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rightWeight_at_cutoff) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.rightWeight_at_cutoff.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.RightCutoff.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RightCutoff

namespace LeftDerivativeNonneg

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t → 0 ≤ s →
    R.readout () () 0 (s / t - abelKernel s (P ^ s) t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num) le_rfl

def family : Registration arena (type_of% @leftWeight_deriv_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@leftWeight_deriv_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@leftWeight_deriv_nonneg) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.leftWeight_deriv_nonneg.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.LeftDerivativeNonneg.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
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

end LeftDerivativeNonneg

namespace PrimeWeightSplit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s x : ℝ}, 0 < P → P ≤ x → 0 ≤ s →
    R.readout () () (∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1 + P ^ s * (p : ℝ) ^ (-s)))
      (s * ((Nat.primeCounting ⌊P⌋₊ : ℝ) * log P - Chebyshev.theta P) + remainder P s x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (x := 1) (by norm_num) le_rfl le_rfl

def family : Registration arena (type_of% @prime_weight_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_weight_split, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_weight_split) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.prime_weight_split.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight.PrimeWeightSplit.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
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

end PrimeWeightSplit

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
