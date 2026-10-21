import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.KummerRatio.Series
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.KummerRatio.Defs
open _root_.D5.S3.Analytic.KummerRatio.Series
open LeanInformationAudit Filter Topology
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Analytic.KummerRatio.Series

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def stepReadout : Realization signature :=
  realize signature (fun _ _ x => if x = 0 then 0 else 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  change kummer 1 1 0 ≠ kummer 1 1 1
  rw [kummer_zero]
  have H := (summable_kummer 1 1 1 (by norm_num)).sum_le_tsum ({0, 1} : Finset ℕ)
    (fun n _ => mul_nonneg
      (div_nonneg (ascPochhammer_pos n (1 : ℝ) zero_lt_one).le
        (mul_nonneg (ascPochhammer_pos n (1 : ℝ) zero_lt_one).le (by positivity)))
      (by positivity))
  change (∑ n ∈ ({0, 1} : Finset ℕ), kummerCoeff 1 1 n * (1 : ℝ) ^ n) ≤ kummer 1 1 1 at H
  norm_num [kummerCoeff] at H
  linarith

namespace Zero
def arena : Arena where
  signature := signature
  Law R := ∀ (s c : ℝ), R.readout () ⟨s, c⟩ 0 = 1
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := h 1 1
  norm_num [zeroReadout, realize] at H
def family : Registration arena (type_of% (@kummer_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kummer_zero, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kummer_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Series.Zero.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Series.Zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Series
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Zero

namespace Positive
def arena : Arena where
  signature := signature
  Law R := ∀ {s c x : ℝ} (_hs : 0 ≤ s) (_hc : 0 < c) (_hx : 0 ≤ x),
    1 ≤ R.readout () ⟨s, c⟩ x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := @h 1 1 0 (by norm_num) (by norm_num) (by norm_num)
  norm_num [zeroReadout, realize] at H
def family : Registration arena (type_of% (@one_le_kummer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_le_kummer, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@one_le_kummer) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Series.Positive.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Series.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Series
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positive

namespace Derivative
def arena : Arena where
  signature := signature
  Law R := ∀ (s : ℝ) {c : ℝ} (_hc : 0 < c) (x : ℝ),
    HasDerivAt (fun y => R.readout () ⟨s, c⟩ y)
      (s / c * kummer (s + 1) (c + 1) x) x
private theorem rejected_law : ¬ arena.Law oneReadout := by
  intro h
  have H := @h 1 1 (by norm_num) 0
  have H' : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 1 0 := by
    simpa [oneReadout, realize, kummer_zero] using H
  have he := H'.unique (hasDerivAt_const 0 (1 : ℝ))
  norm_num at he
def family : Registration arena (type_of% (@hasDerivAt_kummer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_kummer, oneReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual oneReadout rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_kummer) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Series.Derivative.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Series.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Series
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Derivative

namespace Continuous
def arena : Arena where
  signature := signature
  Law R := ∀ (s : ℝ) {c : ℝ} (_hc : 0 < c),
    Continuous (fun y => R.readout () ⟨s, c⟩ y)
private theorem rejected_law : ¬ arena.Law stepReadout := by
  intro h
  have H := @h 1 1 (by norm_num)
  change Continuous (fun y : ℝ => if y = 0 then (0 : ℝ) else 1) at H
  have ht := H.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : (fun n : ℕ => if (1 / ((n : ℝ) + 1)) = 0 then (0 : ℝ) else 1) =
      (fun _ : ℕ => (1 : ℝ)) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp [hn]
  change Tendsto (fun n : ℕ => if (1 / ((n : ℝ) + 1)) = 0 then (0 : ℝ) else 1)
    atTop (𝓝 (if (0 : ℝ) = 0 then (0 : ℝ) else 1)) at ht
  rw [he] at ht
  have hz := tendsto_nhds_unique ht (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  norm_num at hz
def family : Registration arena (type_of% (@continuous_kummer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuous_kummer, stepReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual stepReadout rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_kummer) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Series.Continuous.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Series.Continuous.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Series
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Continuous

namespace Equation
def arena : Arena where
  signature := signature
  Law R := ∀ (s : ℝ) {c : ℝ} (_hc : 0 < c) (x : ℝ),
    x * (s / c * ((s + 1) / (c + 1) * kummer (s + 2) (c + 2) x)) +
      (c - x) * (s / c * kummer (s + 1) (c + 1) x) -
      s * R.readout () ⟨s, c⟩ x = 0
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := @h 1 1 (by norm_num) 0
  norm_num [zeroReadout, realize, kummer_zero] at H
def family : Registration arena (type_of% (@kummer_ode)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kummer_ode, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kummer_ode) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Series.Equation.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Series.Equation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Series
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Equation

namespace Contiguous
def arena : Arena where
  signature := signature
  Law R := ∀ (s : ℝ) {c : ℝ} (_hc : 0 < c) (x : ℝ),
    R.readout () ⟨s, c⟩ x = kummer s (c + 1) x +
      s * x / (c * (c + 1)) * kummer (s + 1) (c + 2) x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := @h 1 1 (by norm_num) 0
  norm_num [zeroReadout, realize, kummer_zero] at H
def family : Registration arena (type_of% (@kummer_contiguous)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kummer_contiguous, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kummer_contiguous) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Series.Contiguous.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Series.Contiguous.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => kummer p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Series
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Contiguous

namespace Summability
abbrev seqSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℕ) (fun _ => ℝ)
def seqActual : Realization seqSignature :=
  realize seqSignature (fun _ p n => kummerCoeff p.1 p.2.1 n * p.2.2 ^ n) (fun e => nomatch e)
def seqRejected : Realization seqSignature :=
  realize seqSignature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := seqSignature
  Law R := ∀ (s c x : ℝ) (_hc : 0 < c), Summable (fun n => R.readout () ⟨s, c, x⟩ n)
private theorem rejected_law : ¬ arena.Law seqRejected := by
  intro h
  have H := h 1 1 1 (by norm_num)
  norm_num [seqRejected, realize, summable_const_iff] at H
private theorem dependence : ObservationalDependence seqSignature seqActual := by
  intro i
  exact ⟨⟨1, 1, 0⟩, 0, 1, by norm_num [seqActual, realize, kummerCoeff]⟩
def family : Registration arena (type_of% (@summable_kummer)) where
  actual := seqActual
  bridge := Iff.rfl
  variation := ⟨@summable_kummer, seqRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law seqActual seqRejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable_kummer) (Realization seqSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.KummerRatio.Series.Summability.unit
  realizationName := `Reg.D5.S3.Analytic.KummerRatio.Series.Summability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seqSignature
    (fun _ p n => kummerCoeff p.1 p.2.1 n * p.2.2 ^ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.KummerRatio.Series
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Summability

end Reg.D5.S3.Analytic.KummerRatio.Series
