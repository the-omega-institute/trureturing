import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.BesselRedheffer.Series
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.BesselRedheffer.Defs
open _root_.D5.S3.Analytic.BesselRedheffer.Series
open LeanInformationAudit Filter Topology

noncomputable section
namespace Reg.D5.S3.Analytic.BesselRedheffer.Series

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def stepReadout : Realization signature :=
  realize signature (fun _ _ x => if x = 0 then 0 else 1) (fun e => nomatch e)
def shiftedReadout : Realization signature :=
  realize signature (fun _ ν x => nbessel ν x + 1) (fun e => nomatch e)

private theorem first_derivative_not_zero :
    (fun y : ℝ => -y / (2 * ((0 : ℝ) + 1)) * nbessel (0 + 1) y) ≠ (fun _ => 0) := by
  intro he
  have hd := hasDerivAt_nbessel_deriv (ν := 0) (by norm_num) 0
  rw [he] at hd
  have hn := hd.unique (hasDerivAt_const 0 (0 : ℝ))
  norm_num [nbessel_zero] at hn

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have hne : ∃ x : ℝ, nbessel 0 0 ≠ nbessel 0 x := by
    by_contra! hn
    have he : nbessel 0 = fun _ => 1 := by
      funext x
      simpa only [nbessel_zero] using (hn x).symm
    apply first_derivative_not_zero
    funext x
    have hd := hasDerivAt_nbessel (ν := 0) (by norm_num) x
    rw [he] at hd
    exact hd.unique (hasDerivAt_const x (1 : ℝ))
  obtain ⟨x, hx⟩ := hne
  exact ⟨0, 0, x, hx⟩

namespace Zero

def arena : Arena where
  signature := signature
  Law R := ∀ ν : ℝ, R.readout () ν 0 = 1
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := h 0
  norm_num [zeroReadout, realize] at H
def family : Registration arena (type_of% (@nbessel_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nbessel_zero, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nbessel_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Zero.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Zero

namespace Derivative

def arena : Arena where
  signature := signature
  Law R := ∀ {ν : ℝ} (_hν : -1 < ν) (x : ℝ),
    HasDerivAt (fun y => R.readout () ν y)
      (-x / (2 * (ν + 1)) * nbessel (ν + 1) x) x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  apply first_derivative_not_zero
  funext x
  have hd := @h 0 (by norm_num) x
  exact hd.unique (hasDerivAt_const x (0 : ℝ))
def family : Registration arena (type_of% (@hasDerivAt_nbessel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_nbessel, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_nbessel) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Derivative.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
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
  Law R := ∀ {ν : ℝ} (_hν : -1 < ν),
    Continuous (fun y => R.readout () ν y)
private theorem rejected_law : ¬ arena.Law stepReadout := by
  intro h
  have H := @h 0 (by norm_num)
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
def family : Registration arena (type_of% (@continuous_nbessel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@continuous_nbessel, stepReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual stepReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_nbessel) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Continuous.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Continuous.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Continuous

namespace LocalPositive

def arena : Arena where
  signature := signature
  Law R := ∀ {ν : ℝ} (_hν : -1 < ν),
    ∀ᶠ x in 𝓝 (0 : ℝ), 0 < R.readout () ν x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := @h 0 (by norm_num)
  have hz := H.self_of_nhds
  norm_num [zeroReadout, realize] at hz
def family : Registration arena (type_of% (@nbessel_pos_near_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nbessel_pos_near_zero, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nbessel_pos_near_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.LocalPositive.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.LocalPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end LocalPositive

namespace Contiguous

def arena : Arena where
  signature := signature
  Law R := ∀ {ν : ℝ} (_hν : -1 < ν) (x : ℝ),
    R.readout () ν x = nbessel (ν + 1) x -
      x ^ 2 / (4 * (ν + 1) * (ν + 2)) * nbessel (ν + 2) x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := @h 0 (by norm_num) 0
  norm_num [zeroReadout, realize, nbessel_zero] at H
def family : Registration arena (type_of% (@nbessel_contiguous)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nbessel_contiguous, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nbessel_contiguous) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Contiguous.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Contiguous.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Contiguous

namespace Equation

def arena : Arena where
  signature := signature
  Law R := ∀ {ν : ℝ} (_hν : -1 < ν) (x : ℝ),
    x * (-1 / (2 * (ν + 1)) * nbessel (ν + 1) x +
      x ^ 2 / (4 * (ν + 1) * (ν + 2)) * nbessel (ν + 2) x) +
    (2 * ν + 1) * (-x / (2 * (ν + 1)) * nbessel (ν + 1) x) +
    x * R.readout () ν x = 0
private theorem rejected_law : ¬ arena.Law shiftedReadout := by
  intro h
  have H := @h 0 (by norm_num) 1
  have H0 := nbessel_ode (ν := 0) (by norm_num) 1
  dsimp [shiftedReadout, realize] at H
  norm_num at H H0
  linarith
def family : Registration arena (type_of% (@nbessel_ode)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nbessel_ode, shiftedReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shiftedReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nbessel_ode) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Equation.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Equation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ν x => nbessel ν x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Equation

namespace Summability
abbrev seqSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℕ) (fun _ => ℝ)
def seqActual : Realization seqSignature :=
  realize seqSignature (fun _ p n => (-(p.2 ^ 2) / 4) ^ n /
    ((n.factorial : ℝ) * (ascPochhammer ℝ n).eval (p.1 + 1))) (fun e => nomatch e)
def seqRejected : Realization seqSignature :=
  realize seqSignature (fun _ _ _ => 1) (fun e => nomatch e)
private theorem dependence : ObservationalDependence seqSignature seqActual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  norm_num [seqActual, realize]

def arena : Arena where
  signature := seqSignature
  Law R := ∀ {ν : ℝ} (_hν : -1 < ν) (x : ℝ),
    Summable (fun n => R.readout () ⟨ν, x⟩ n)
private theorem rejected_law : ¬ arena.Law seqRejected := by
  intro h
  have H := @h 0 (by norm_num) 0
  norm_num [seqRejected, realize, summable_const_iff] at H
def family : Registration arena (type_of% (@summable_nbessel)) where
  actual := seqActual
  bridge := Iff.rfl
  variation := ⟨@summable_nbessel, seqRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law seqActual seqRejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable_nbessel) (Realization seqSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Summability.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.Summability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seqSignature (fun _ p n => (-(p.2 ^ 2) / 4) ^ n /
    ((n.factorial : ℝ) * (ascPochhammer ℝ n).eval (p.1 + 1))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Summability

namespace SecondDerivative
abbrev derivativeSignature : Signature := signature
def derivativeActual : Realization derivativeSignature :=
  realize derivativeSignature (fun _ ν x => -x / (2 * (ν + 1)) * nbessel (ν + 1) x)
    (fun e => nomatch e)
private theorem dependence : ObservationalDependence derivativeSignature derivativeActual := by
  intro i
  have hne : ∃ x : ℝ, -x / (2 * ((0 : ℝ) + 1)) * nbessel (0 + 1) x ≠ 0 := by
    by_contra! hn
    apply first_derivative_not_zero
    exact funext hn
  obtain ⟨x, hx⟩ := hne
  refine ⟨0, 0, x, ?_⟩
  simpa [derivativeActual, realize] using hx.symm

def arena : Arena where
  signature := derivativeSignature
  Law R := ∀ {ν : ℝ} (_hν : -1 < ν) (x : ℝ),
    HasDerivAt (fun y => R.readout () ν y)
      (-1 / (2 * (ν + 1)) * nbessel (ν + 1) x +
        x ^ 2 / (4 * (ν + 1) * (ν + 2)) * nbessel (ν + 2) x) x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have H := @h 0 (by norm_num) 0
  have he := H.unique (hasDerivAt_const 0 (0 : ℝ))
  norm_num [nbessel_zero] at he
def family : Registration arena (type_of% (@hasDerivAt_nbessel_deriv)) where
  actual := derivativeActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_nbessel_deriv, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law derivativeActual zeroReadout rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_nbessel_deriv) (Realization derivativeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.SecondDerivative.unit
  realizationName := `Reg.D5.S3.Analytic.BesselRedheffer.Series.SecondDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize derivativeSignature (fun _ ν x => -x / (2 * (ν + 1)) * nbessel (ν + 1) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.BesselRedheffer.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SecondDerivative

end Reg.D5.S3.Analytic.BesselRedheffer.Series
