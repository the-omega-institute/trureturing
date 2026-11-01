import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
import Reg.Support.SingleDependentReadout

/-! Source-only candidates. The selectors below are proposed raw-expression paths,
not compiler-derived binding evidence. Each law retains the complete source result. -/

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy

abbrev normSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def normActual : Realization normSignature :=
  realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def normRejected : Realization normSignature :=
  realize normSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem normDependence : ObservationalDependence normSignature normActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

abbrev expSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def expActual : Realization expSignature :=
  realize expSignature (fun _ _ t => Real.exp t) (fun e => nomatch e)

def expRejected : Realization expSignature :=
  realize expSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem expDependence : ObservationalDependence expSignature expActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp 0 ≠ Real.exp 1
  intro h
  have h01 := Real.exp_injective h
  norm_num at h01

abbrev realPartSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def realPartActual : Realization realPartSignature :=
  realize realPartSignature (fun _ _ z => z.re) (fun e => nomatch e)

def realPartRejected : Realization realPartSignature :=
  realize realPartSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem realPartDependence : ObservationalDependence realPartSignature realPartActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

abbrev shiftedArena : Arena where
  signature := normSignature
  Law R := ∀ {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (s : ℝ),
    Integrable (fun v : ℝ => star («prefix» x a (v + s)) * «prefix» x a v) ∧
    Integrable (fun v : ℝ => ‖«prefix» x a v‖ ^ 2) ∧
    (∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) =
      -(∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v) ∧
    R.readout () () (∑ i, ∑ j, star (a i) * a j * ((max (x i - x j - s) 0 : ℝ) : ℂ)) ≤
      ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2

private theorem shiftedRejectedLaw : ¬ shiftedArena.{u}.Law normRejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by simp) 0
  have hb := h0.2.2.2
  norm_num [normRejected, realize, «prefix»] at hb

def shiftedFamily : Registration shiftedArena.{u}
    (type_of% @shifted_hinge_prefix_energy.{u}) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@shifted_hinge_prefix_energy.{u}, normRejected, shiftedRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    shiftedArena.Law normActual normRejected shiftedRejectedLaw
  dependence := normDependence

def shiftedAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shifted_hinge_prefix_energy.{u}) (Realization normSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.shifted_hinge_prefix_energy.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.shiftedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shiftedArena⟩
  objectArena := .source ⟨shiftedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftedArena ⟨shiftedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev windowArena : Arena where
  signature := expSignature
  Law R := ∀ (lam D t : ℝ) (hlam : 0 < lam)
    (hD : 0 ≤ D) (ht : |t| ≤ D),
    IntegrableOn (fun s : ℝ => max (t - s) 0 * Real.exp (-lam * |s|)) (Icc (-D) D) ∧
    R.readout () () (-lam * |t|) = Real.exp (-lam * D) +
      lam * Real.exp (-lam * D) * (t + D) +
      lam ^ 2 * (∫ s in Icc (-D) D, max (t - s) 0 * Real.exp (-lam * |s|)) -
      2 * lam * max t 0

private theorem windowRejectedLaw : ¬ windowArena.Law expRejected := by
  intro h
  have h0 := h 1 0 0 (by norm_num) (by norm_num) (by norm_num)
  have hb := h0.2
  norm_num [expRejected, realize] at hb

def windowFamily : Registration windowArena
    (type_of% @finite_window_exponential_hinge) where
  actual := expActual
  bridge := Iff.rfl
  variation := ⟨@finite_window_exponential_hinge, expRejected, windowRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    windowArena.Law expActual expRejected windowRejectedLaw
  dependence := expDependence

def windowAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_window_exponential_hinge) (Realization expSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.finite_window_exponential_hinge.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.windowFamily
  realizationSource := none
  generated := false
  arena := .source ⟨windowArena⟩
  objectArena := .source ⟨windowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowArena ⟨windowFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize expSignature (fun _ _ t => Real.exp t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev energyArena : Arena where
  signature := normSignature
  Law R := ∀ {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (lam D : ℝ) (hlam : 0 < lam) (hD : 0 ≤ D)
    (hx : ∀ i j, |x i - x j| ≤ D),
    let F := «prefix» x a
    let E : ℝ := ∫ v : ℝ, ‖F v‖ ^ 2
    let C : ℝ → ℂ := fun s => ∫ v : ℝ, star (F (v + s)) * F v
    Integrable (fun v : ℝ => (R.readout () () (F v)) ^ 2) ∧
    (∀ s : ℝ, Integrable (fun v : ℝ => star (F (v + s)) * F v)) ∧
    Continuous C ∧
    IntegrableOn (fun s => (Real.exp (-lam * |s|) : ℂ) * C s) (Icc (-D) D) ∧
    (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ)) =
      (2 * lam : ℂ) * (E : ℂ) -
        (lam ^ 2 : ℂ) * (∫ s in Icc (-D) D, (Real.exp (-lam * |s|) : ℂ) * C s)

private theorem energyRejectedLaw : ¬ energyArena.{u}.Law normRejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by simp) 1 0 (by norm_num) (by norm_num) (by intro i; cases i.down)
  have hi : Integrable (fun _ : ℝ => (1 : ℝ)) := by
    simpa only [normRejected, realize, one_pow] using h0.1
  have hf := (integrable_const_iff_isFiniteMeasure
    (μ := (volume : Measure ℝ)) (by norm_num : (1 : ℝ) ≠ 0)).mp hi
  have hfin := @measure_lt_top ℝ _ volume hf univ
  simpa using hfin

def energyFamily : Registration energyArena.{u}
    (type_of% @exponential_prefix_energy.{u}) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨@exponential_prefix_energy.{u}, normRejected, energyRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    energyArena.Law normActual normRejected energyRejectedLaw
  dependence := normDependence

def energyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exponential_prefix_energy.{u}) (Realization normSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.exponential_prefix_energy.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.energyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨energyArena⟩
  objectArena := .source ⟨energyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source energyArena ⟨energyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize normSignature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev coercivityArena : Arena where
  signature := realPartSignature
  Law R := ∀ {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (lam D : ℝ) (hlam : 0 < lam) (hD : 0 ≤ D)
    (hx : ∀ i j, |x i - x j| ≤ D),
    2 * lam * Real.exp (-lam * D) * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) ≤
      R.readout () () (∑ i, ∑ j, star (a i) * a j * (Real.exp (-lam * |x i - x j|) : ℂ))

private theorem coercivityRejectedLaw : ¬ coercivityArena.{u}.Law realPartRejected := by
  intro h
  have hb := @h (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by simp) 1 0 (by norm_num) (by norm_num) (by intro i; cases i.down)
  norm_num [realPartRejected, realize, «prefix»] at hb

def coercivityFamily : Registration coercivityArena.{u}
    (type_of% @exponential_prefix_coercivity.{u}) where
  actual := realPartActual
  bridge := Iff.rfl
  variation := ⟨@exponential_prefix_coercivity.{u}, realPartRejected, coercivityRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coercivityArena.Law realPartActual realPartRejected coercivityRejectedLaw
  dependence := realPartDependence

def coercivityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exponential_prefix_coercivity.{u}) (Realization realPartSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.exponential_prefix_coercivity.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy.coercivityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨coercivityArena⟩
  objectArena := .source ⟨coercivityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coercivityArena ⟨coercivityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realPartSignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
