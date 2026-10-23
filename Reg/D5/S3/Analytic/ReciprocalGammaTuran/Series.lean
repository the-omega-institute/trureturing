import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ReciprocalGammaTuran.Series
import Reg.Support.SingleDependentReadout

noncomputable section
namespace Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Defs
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Series
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Topology

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
  have h₁ := Real.Gamma_neg_nat_eq_zero 1
  have h₂ := Real.Gamma_neg_nat_eq_zero 2
  norm_num [rgamma] at h₁ h₂
  norm_num [turanCoeff, Finset.sum_range_succ, h₁, h₂, rgamma,
    Real.Gamma_zero, Real.Gamma_one] at hh

namespace FormalCauchy
def arena : Arena where
  signature := formalSignature
  Law R := ∀ (g : ℕ → ℝ) (μ α β : ℝ) (m : ℕ),
    PowerSeries.coeff m
      (R.readout () g (μ+α) * formalSeries g (μ+β) -
        formalSeries g μ * formalSeries g (μ+α+β)) = turanCoeff g μ α β m
private theorem rejected_law : ¬ arena.Law formalZero := by
  intro h
  have he := h (fun _ => 1) 0 1 1 0
  norm_num [formalZero, realize, formalSeries, turanCoeff, rgamma, Real.Gamma_zero, Real.Gamma_one] at he
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
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end FormalCauchy

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
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms audit
end BoundaryIdentification

end Reg.D5.S3.Analytic.ReciprocalGammaTuran.Series
