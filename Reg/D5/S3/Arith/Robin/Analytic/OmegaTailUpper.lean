import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTailUpper
import Reg.Support.SingleDependentReadout

/-! Source telescopes for the upper exponential bound and its zero-rate limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real MeasureTheory Set LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper

namespace UpperBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (lambda : ℝ), lambda ≤ 1 → ∀ {s epsilon : ℝ},
    1 < s → 0 < epsilon → ∀ᶠ x : ℝ in atTop,
      R.readout () () (tailCount lambda x : ℝ)
        (exp ((rate lambda s + epsilon) * scale x))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : ∀ᶠ x : ℝ in atTop, False :=
    h 0 (by norm_num) (s := 2) (epsilon := 1) (by norm_num) (by norm_num)
  obtain ⟨x, hx⟩ := hh.exists
  exact hx

def family : Registration arena (type_of% @upper_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@upper_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@upper_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.upper_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.UpperBound.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UpperBound

namespace ZeroRate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () ()
    (fun x : ℝ => log (1 + (tailCount 1 x : ℝ)) / scale x) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
    intro he
    have he' := congrFun (congrFun he atTop) (𝓝 (0 : ℝ))
    have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp he' tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.result.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.ZeroRate.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
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

end ZeroRate

namespace ScalePositive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ}, exp 1 < x → R.readout () () 0 (scale x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (x := exp 1 + 1) (by linarith)

def family : Registration arena (type_of% @scale_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scale_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
    exact lt_irrefl _ hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@scale_pos) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.scale_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.ScalePositive.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
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


end ScalePositive

namespace OptimizerPositive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → R.readout () () 0 (a s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (by norm_num)

def family : Registration arena (type_of% @a_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@a_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℝ) < 1)
    exact lt_irrefl _ hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@a_pos) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.a_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.OptimizerPositive.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
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


end OptimizerPositive

namespace ScaleDivergence

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () scale atTop atTop

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @scale_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scale_tendsto, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩
    intro he
    have he' := congrFun (congrFun he atTop) (𝓝 (0 : ℝ))
    have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp he' tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@scale_tendsto) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.scale_tendsto.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.ScaleDivergence.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
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


end ScaleDivergence

namespace PowerKernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s c : ℝ}, 1 < s → 0 < c →
    IntegrableOn (fun u : ℝ => s * c / (u ^ s + c)) (Ioi 0) ∧
      R.readout () () (∫ u in Ioi (0 : ℝ), s * c / (u ^ s + c))
        (π * c ^ (1 / s) / sin (π / s))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (s := 2) (c := 1) (by norm_num) (by norm_num)).2

def family : Registration arena (type_of% @power_kernel_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_kernel_integral, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) (Eq.refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@power_kernel_integral) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.power_kernel_integral.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.PowerKernel.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end PowerKernel

namespace LogWeightDerivative

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => ℝ → ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s z t : ℝ}, 0 < z → 0 < t →
    R.readout () () (logWeight s z) (-abelKernel s z t) t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 0) (z := 1) (t := 1) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @logWeight_deriv) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logWeight_deriv, rejected, rejected_law⟩
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
    (@logWeight_deriv) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.logWeight_deriv.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.LogWeightDerivative.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
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


end LogWeightDerivative

namespace RankinExponential

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s z x T : ℝ}, 1 < s → 1 ≤ z → 0 < x →
    R.readout () ()
      (((Finset.Icc 1 ⌊x⌋₊).filter (fun n => T <
        (ArithmeticFunction.cardDistinctFactors n : ℝ))).card : ℝ)
      (exp (s * log x - T * log z +
        log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) +
        ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, log (1 + z * (p : ℝ) ^ (-s))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (z := 1) (x := 1) (T := 0) (by norm_num) le_rfl (by norm_num)

def family : Registration arena (type_of% @rankin_exponential_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rankin_exponential_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rankin_exponential_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.rankin_exponential_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.RankinExponential.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
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

end RankinExponential

namespace AbelContinuity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => ContinuousOn f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s z a b : ℝ}, 0 < z → 0 < a →
    R.readout () () (abelKernel s z) (Set.Icc a b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 0) (z := 1) (a := 1) (b := 2) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @abelKernel_continuousOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abelKernel_continuousOn, rejected, rejected_law⟩
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
    (@abelKernel_continuousOn) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper.abelKernel_continuousOn.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper.AbelContinuity.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTailUpper
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

end AbelContinuity

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
