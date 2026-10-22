import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ReciprocalGammaTuran.Series
import Reg.Support.SingleDependentReadout

noncomputable section
namespace Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Defs
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Series
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ b => F b) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)
def oneReadout : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro hh
  have h := congrFun hh 0
  norm_num [actual, realize, F, zero_pow_eq, rgamma, Real.Gamma_zero, Real.Gamma_one] at h

namespace Entire
def arena : Arena where
  signature := signature
  Law R := ∀ b : ℝ, HasFPowerSeriesOnBall (R.readout () () b)
    (FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => rgamma ((n : ℝ) + b))) 0 ⊤
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have hh := (h 1).hasSum (show (0 : ℝ) ∈ Metric.eball (0 : ℝ) ⊤ from by simp)
  have he := (hasSum_series 1 0).unique (by simpa only
    [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hh)
  norm_num [zeroReadout, realize, F, zero_pow_eq, rgamma, Real.Gamma_one] at he
def family : Registration arena (type_of% @entire_series) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨entire_series, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entire_series) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.Entire.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.Entire.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => F b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Entire

namespace Convergence
def arena : Arena where
  signature := signature
  Law R := ∀ b x : ℝ, HasSum (fun n : ℕ => rgamma ((n : ℝ) + b) * x ^ n)
    (R.readout () () b x)
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have he := (hasSum_series 1 0).unique (h 1 0)
  norm_num [zeroReadout, realize, F, zero_pow_eq, rgamma, Real.Gamma_one] at he
def family : Registration arena (type_of% @hasSum_series) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hasSum_series, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasSum_series) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.Convergence.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.Convergence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => F b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Convergence

namespace ZeroParameter
def arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, R.readout () () 0 x = x * Real.exp x
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have he := h 1
  norm_num [zeroReadout, realize] at he
  exact (Real.exp_ne_zero 1) he.symm
def family : Registration arena (type_of% @F_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨F_zero, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@F_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.ZeroParameter.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.ZeroParameter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => F b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end ZeroParameter

namespace Derivative
def arena : Arena where
  signature := signature
  Law R := ∀ b x : ℝ, HasDerivAt (R.readout () () b)
    (R.readout () () b x + (1-b) * R.readout () () (b+1) x) x
private theorem rejected_law : ¬ arena.Law oneReadout := by
  intro h
  have he := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).unique (h 0 0)
  norm_num [oneReadout, realize] at he
def family : Registration arena (type_of% @hasDerivAt_F) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hasDerivAt_F, oneReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual oneReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_F) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.Derivative.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => F b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end Derivative

namespace DifferentialEquation
def arena : Arena where
  signature := signature
  Law R := ∀ b x : ℝ, x * deriv (R.readout () () b) x =
    (x+1-b) * R.readout () () b x + (b-1) * rgamma b
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have he := h 2 0
  have h₂ : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  norm_num [zeroReadout, realize, rgamma, h₂] at he
def family : Registration arena (type_of% @differential_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨differential_recurrence, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@differential_recurrence) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.DifferentialEquation.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.DifferentialEquation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => F b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end DifferentialEquation

namespace CauchyConvergence
def arena : Arena where
  signature := signature
  Law R := ∀ μ α β x : ℝ, HasSum
    (fun m : ℕ => turanCoeff (fun _ => 1) μ α β m * x ^ m)
    (R.readout () () (μ+α) x * R.readout () () (μ+β) x -
      R.readout () () μ x * R.readout () () (μ+α+β) x)
private theorem rejected_law : ¬ arena.Law zeroReadout := by
  intro h
  have he := (hasSum_turanCoeff 0 1 1 0).unique (h 0 1 1 0)
  norm_num [zeroReadout, realize, F, zero_pow_eq, rgamma, Real.Gamma_one, Real.Gamma_zero] at he
def family : Registration arena (type_of% @hasSum_turanCoeff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hasSum_turanCoeff, zeroReadout, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual zeroReadout rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasSum_turanCoeff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.CauchyConvergence.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.CauchyConvergence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => F b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end CauchyConvergence

abbrev formalSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ → ℝ) (fun _ => ℝ) (fun _ => PowerSeries ℝ)
def formalActual : Realization formalSignature :=
  realize formalSignature (fun _ g b => formalSeries g b) (fun e => nomatch e)
def formalZero : Realization formalSignature :=
  realize formalSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem formal_dependence : ObservationalDependence formalSignature formalActual := by
  intro i
  refine ⟨(fun _ => 1), 0, 1, ?_⟩
  intro hh
  have h := congrArg (PowerSeries.coeff 0) hh
  norm_num [formalActual, realize, formalSeries, rgamma, Real.Gamma_zero, Real.Gamma_one] at h

abbrev unitFormalSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => PowerSeries ℝ)
def unitFormalActual : Realization unitFormalSignature :=
  realize unitFormalSignature (fun _ _ b => formalSeries (fun _ => 1) b) (fun e => nomatch e)
def unitFormalZero : Realization unitFormalSignature :=
  realize unitFormalSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem unitFormal_dependence : ObservationalDependence unitFormalSignature unitFormalActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro hh
  have h := congrArg (PowerSeries.coeff 0) hh
  norm_num [unitFormalActual, realize, formalSeries, rgamma, Real.Gamma_zero, Real.Gamma_one] at h

abbrev coefficientSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)
def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ t m => d t m) (fun e => nomatch e)
def coefficientBad : Realization coefficientSignature :=
  realize coefficientSignature (fun _ t m => d t m + 1) (fun e => nomatch e)
private theorem coefficient_dependence : ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨2, 0, 2, ?_⟩
  intro hh
  change d 2 0 = d 2 2 at hh
  rw [← turanCoeff_one_boundary, ← turanCoeff_one_boundary] at hh
  have h₁ := rgamma_neg_nat 1
  have h₂ := rgamma_neg_nat 2
  norm_num [rgamma] at h₁ h₂
  norm_num [turanCoeff, Finset.sum_range_succ, h₁, h₂, rgamma,
    Real.Gamma_zero, Real.Gamma_one] at hh

abbrev boundarySignature : Signature := unitFormalSignature
def boundaryActual : Realization boundarySignature :=
  realize boundarySignature (fun _ _ t => boundarySeries t) (fun e => nomatch e)
def boundaryBad : Realization boundarySignature :=
  realize boundarySignature (fun _ _ t => boundarySeries t + 1) (fun e => nomatch e)
private theorem boundary_dependence : ObservationalDependence boundarySignature boundaryActual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  intro hh
  have he := congrArg (PowerSeries.coeff 2) hh
  change d 0 2 = d 2 2 at he
  rw [← turanCoeff_one_boundary, ← turanCoeff_one_boundary] at he
  have h₁ := rgamma_neg_nat 1
  have h₂ := rgamma_neg_nat 2
  norm_num [rgamma] at h₁ h₂
  norm_num [turanCoeff, Finset.sum_range_succ, h₁, h₂, rgamma,
    Real.Gamma_zero, Real.Gamma_one] at he

namespace FormalCauchy
def arena : Arena where
  signature := formalSignature
  Law R := ∀ (g : ℕ → ℝ) (μ α β : ℝ) (m : ℕ),
    PowerSeries.coeff m
      (R.readout () g (μ+α) * R.readout () g (μ+β) -
        R.readout () g μ * R.readout () g (μ+α+β)) = turanCoeff g μ α β m
private theorem rejected_law : ¬ arena.Law formalZero := by
  intro h
  have he := h (fun _ => 1) 0 1 1 0
  norm_num [formalZero, realize, turanCoeff, rgamma, Real.Gamma_zero, Real.Gamma_one] at he
def family : Registration arena (type_of% @coeff_mul) where
  actual := formalActual
  bridge := Iff.rfl
  variation := ⟨coeff_mul, formalZero, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law formalActual formalZero rejected_law
  dependence := formal_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coeff_mul) (Realization formalSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.FormalCauchy.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.FormalCauchy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize formalSignature (fun _ g b => formalSeries g b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end FormalCauchy

namespace FormalEquation
def arena : Arena where
  signature := unitFormalSignature
  Law R := ∀ b : ℝ,
    PowerSeries.X * PowerSeries.derivative (R.readout () () b) =
      (PowerSeries.X + PowerSeries.C (1-b)) * R.readout () () b +
        PowerSeries.C ((b-1) * rgamma b)
private theorem rejected_law : ¬ arena.Law unitFormalZero := by
  intro h
  have he := congrArg (PowerSeries.coeff 0) (h 2)
  have h₂ : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  norm_num [unitFormalZero, realize, rgamma, h₂] at he
def family : Registration arena (type_of% @formal_recurrence) where
  actual := unitFormalActual
  bridge := Iff.rfl
  variation := ⟨formal_recurrence, unitFormalZero, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law unitFormalActual unitFormalZero rejected_law
  dependence := unitFormal_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@formal_recurrence) (Realization unitFormalSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.FormalEquation.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.FormalEquation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize unitFormalSignature (fun _ _ b => formalSeries (fun _ => 1) b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end FormalEquation

namespace BoundaryIdentification
def arena : Arena where
  signature := coefficientSignature
  Law R := ∀ (t : ℝ) (m : ℕ),
    turanCoeff (fun _ => 1) (-t) t t m = R.readout () t m
private theorem rejected_law : ¬ arena.Law coefficientBad := by
  intro h
  have he := h 0 0
  norm_num [coefficientBad, realize, d, boundarySeries, pow_two, turanCoeff] at he
def family : Registration arena (type_of% @turanCoeff_one_boundary) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨turanCoeff_one_boundary, coefficientBad, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law coefficientActual coefficientBad rejected_law
  dependence := coefficient_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@turanCoeff_one_boundary) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.BoundaryIdentification.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.BoundaryIdentification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ t m => d t m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end BoundaryIdentification

namespace BoundaryEquation
def arena : Arena where
  signature := boundarySignature
  Law R := ∀ t : ℝ,
    PowerSeries.X * PowerSeries.derivative (R.readout () () t) =
      2 * (PowerSeries.X + 1) * R.readout () () t +
        PowerSeries.C ((t+1) * rgamma (-t)) * formalSeries (fun _ => 1) t +
        PowerSeries.C ((1-t) * rgamma t) * formalSeries (fun _ => 1) (-t)
private theorem rejected_law : ¬ arena.Law boundaryBad := by
  intro h
  have he := congrArg (PowerSeries.coeff 0) (h 0)
  norm_num [boundaryBad, realize, boundarySeries, pow_two, rgamma, Real.Gamma_zero,
    PowerSeries.derivative_one, map_ofNat] at he
def family : Registration arena (type_of% @boundary_recurrence) where
  actual := boundaryActual
  bridge := Iff.rfl
  variation := ⟨boundary_recurrence, boundaryBad, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law boundaryActual boundaryBad rejected_law
  dependence := boundary_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boundary_recurrence) (Realization boundarySignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.BoundaryEquation.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.BoundaryEquation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundarySignature (fun _ _ t => boundarySeries t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end BoundaryEquation

namespace CoefficientEquation
def arena : Arena where
  signature := coefficientSignature
  Law R := ∀ (t : ℝ) (m : ℕ), 3 ≤ m →
    ((m : ℝ)-2) * R.readout () t m = 2 * R.readout () t (m-1) + r t m
private theorem rejected_law : ¬ arena.Law coefficientBad := by
  intro h
  have he := h 0 3 (by omega)
  norm_num [coefficientBad, realize, d, boundarySeries, pow_two, r, rgamma,
    Real.Gamma_zero] at he
def family : Registration arena (type_of% @coefficient_recurrence) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨coefficient_recurrence, coefficientBad, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law coefficientActual coefficientBad rejected_law
  dependence := coefficient_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_recurrence) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.CoefficientEquation.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series.CoefficientEquation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ t m => d t m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end CoefficientEquation

end Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series
