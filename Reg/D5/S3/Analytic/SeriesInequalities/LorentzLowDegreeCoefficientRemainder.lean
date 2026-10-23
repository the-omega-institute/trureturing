import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder


open LeanInformationAudit Finset Polynomial Complex
open scoped BigOperators

universe u
noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

namespace AuditBernsteinDiskBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    (c : Fin (d + 1) → ℂ) {B p : ℝ} (hc : ∀ i, ‖c i‖ ≤ B)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) {z : ℂ}
    (hz : ‖z - (p : ℂ)‖ ≤ derivativeRadius d ℓ p),
    F.readout () () ((bernsteinRealization d c).eval z) ≤ B * Real.exp (6 * (ℓ : ℝ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h 1 1 (by omega) (by omega) 0 0 0 (by simp) (by norm_num) 0
    (by simp [derivativeRadius])
  norm_num [rejected, realize] at hb
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@bernstein_disk_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bernstein_disk_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bernstein_disk_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinDiskBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinDiskBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditBernsteinDiskBound

namespace AuditCoefficientCauchyBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (P : ℂ[X]) (n : ℕ) {R M : ℝ}
    (hR : 0 < R) (hM : ∀ z : ℂ, ‖z‖ = R → ‖P.eval z‖ ≤ M),
    F.readout () () (P.coeff n) ≤ M / R ^ n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h 0 0 1 0 (by norm_num) (by simp)
  norm_num [rejected, realize] at hb
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@coefficient_cauchy_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_cauchy_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_cauchy_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditCoefficientCauchyBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditCoefficientCauchyBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCoefficientCauchyBound

namespace AuditTaylorCoefficientRemainderBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (r : ℕ),
    ∃ A K : ℝ, 1 ≤ A ∧ 1 ≤ K ∧
      ∀ d D : ℕ, 0 < d → A * (d : ℝ) ≤ D →
        ∀ c : Fin (d + 1) → ℂ, ∀ J : ℕ, J ≤ D →
          F.readout () () (bernsteinCoefficient D J (bernsteinRealization d c -
            truncatedTaylor (bernsteinRealization d c) ((J : ℂ) / D) r)) ≤
            K * ((d : ℝ) / D) ^ (((r : ℝ) + 1) / 2) * ‖c‖
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, K, hA, hK, hb⟩ := h 0
  obtain ⟨D, hD⟩ := exists_nat_ge A
  have hh := hb 1 D (by omega) (by simpa using hD) 0 0 (by omega)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@taylor_coefficient_remainder_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@taylor_coefficient_remainder_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@taylor_coefficient_remainder_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorCoefficientRemainderBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorCoefficientRemainderBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditTaylorCoefficientRemainderBound

namespace AuditTaylorCoefficientRemainder
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (r : ℕ),
    ∃ A K : ℝ, 1 ≤ A ∧ 1 ≤ K ∧
      ∀ d D : ℕ, 0 < d → A * (d : ℝ) ≤ D →
        ∀ c : Fin (d + 1) → ℂ, ∀ J : ℕ, (hJ : J ≤ D) →
          ∃ a : Fin (D + 1) → ℂ,
            bernsteinRealization d c - truncatedTaylor (bernsteinRealization d c)
              ((J : ℂ) / D) r = bernsteinRealization D a ∧
            F.readout () () (a ⟨J, by omega⟩) ≤ K * ((d : ℝ) / D) ^ (((r : ℝ) + 1) / 2) * ‖c‖ ∧
            (d ≤ r → a = 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, K, hA, hK, hb⟩ := h 0
  obtain ⟨D, hD⟩ := exists_nat_ge A
  obtain ⟨a, he, ha, hz⟩ := hb 1 D (by omega) (by simpa using hD) 0 0 (by omega)
  norm_num [rejected, realize] at ha
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@taylor_coefficient_remainder)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@taylor_coefficient_remainder, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@taylor_coefficient_remainder) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorCoefficientRemainder.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorCoefficientRemainder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditTaylorCoefficientRemainder

namespace AuditRadiusProperties
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => (x : ℝ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1),
    0 < derivativeRadius d ℓ p ∧
      (derivativeRadius d ℓ p) ^ 2 / (p * (1 - p) + derivativeRadius d ℓ p)
        ≤ F.readout () () ℓ / d
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (@h 1 1 (by omega) (by omega) 0 (by norm_num)).2
  norm_num [rejected, realize, derivativeRadius] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@radius_properties)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@radius_properties, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radius_properties) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditRadiusProperties.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditRadiusProperties.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => (x : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditRadiusProperties

namespace AuditPolynomialIteratedDeriv
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (P : ℂ[X]) (n : ℕ),
    iteratedDeriv n (fun z : ℂ => P.eval z) = fun z => (derivative^[n] (F.readout () () P)).eval z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := congrFun (h 0 0) 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@polynomial_iterated_deriv)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polynomial_iterated_deriv, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@polynomial_iterated_deriv) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditPolynomialIteratedDeriv.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditPolynomialIteratedDeriv.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditPolynomialIteratedDeriv

namespace AuditBernsteinCoefficientSum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} (s : Finset ι)
    (P : ι → ℂ[X]) (D J : ℕ),
    bernsteinCoefficient (F.readout () () D) J (∑ i ∈ s, P i) = ∑ i ∈ s, bernsteinCoefficient D J (P i)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (ULift Unit) {⟨()⟩} (fun _ => X) 1 1
  norm_num [rejected, realize, bernsteinCoefficient, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@bernstein_coefficient_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bernstein_coefficient_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bernstein_coefficient_sum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinCoefficientSum.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinCoefficientSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditBernsteinCoefficientSum

namespace AuditBernsteinCoefficientCMul
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (D J : ℕ) (a : ℂ) (P : ℂ[X]),
    bernsteinCoefficient D J (C a * P) = F.readout () () a * bernsteinCoefficient D J P
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0 1
  norm_num [rejected, realize, bernsteinCoefficient] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@bernstein_coefficient_C_mul)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bernstein_coefficient_C_mul, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bernstein_coefficient_C_mul) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinCoefficientCMul.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinCoefficientCMul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditBernsteinCoefficientCMul

namespace AuditRealizationDegree
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p x => x.natDegree) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (d : ℕ) (c : Fin (d + 1) → ℂ),
    F.readout () () (bernsteinRealization d c) ≤ d
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, X, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@realization_degree)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realization_degree, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@realization_degree) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditRealizationDegree.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditRealizationDegree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x.natDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditRealizationDegree

namespace AuditTaylorExpansionUpTo
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (P : ℂ[X]) (p : ℂ) {d : ℕ}
    (hdeg : P.natDegree ≤ d),
    F.readout () () P = ∑ ℓ ∈ range (d + 1), C ((P.taylor p).coeff ℓ) * (X - C p) ^ ℓ
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 0 0 (by simp)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@taylor_expansion_up_to)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@taylor_expansion_up_to, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@taylor_expansion_up_to) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorExpansionUpTo.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorExpansionUpTo.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditTaylorExpansionUpTo

namespace AuditTaylorRemainderExpansion
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (P : ℂ[X]) (p : ℂ) {d r : ℕ}
    (hdeg : P.natDegree ≤ d) (hr : r ≤ d),
    F.readout () () P - truncatedTaylor P p r =
      ∑ ℓ ∈ Ico (r + 1) (d + 1), C ((P.taylor p).coeff ℓ) * (X - C p) ^ ℓ
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 0 0 0 (by simp) (by omega)
  norm_num [rejected, realize, truncatedTaylor] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@taylor_remainder_expansion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@taylor_remainder_expansion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@taylor_remainder_expansion) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorRemainderExpansion.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTaylorRemainderExpansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditTaylorRemainderExpansion

namespace AuditTruncatedTaylorExact
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (P : ℂ[X]) (p : ℂ) {r : ℕ}
    (hdeg : P.natDegree ≤ r),
    truncatedTaylor P p r = F.readout () () P
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 0 0 (by simp)
  norm_num [rejected, realize, truncatedTaylor] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@truncated_taylor_exact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@truncated_taylor_exact, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@truncated_taylor_exact) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTruncatedTaylorExact.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTruncatedTaylorExact.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditTruncatedTaylorExact

namespace AuditBernsteinReconstruction
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (P : ℂ[X]) (D : ℕ) (hdeg : P.natDegree ≤ D),
    (∑ J ∈ range (D+1), C (bernsteinCoefficient D J P) * bernsteinPolynomial ℂ D J) = F.readout () () P
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 (by simp)
  norm_num [rejected, realize, bernsteinCoefficient] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@bernstein_reconstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bernstein_reconstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bernstein_reconstruction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinReconstruction.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditBernsteinReconstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditBernsteinReconstruction

namespace AuditTruncatedTaylorDegree
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p x => x.natDegree) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (P : ℂ[X]) (p : ℂ) (r : ℕ),
    F.readout () () (truncatedTaylor P p r) ≤ r
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, X, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@truncated_taylor_degree)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@truncated_taylor_degree, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@truncated_taylor_degree) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTruncatedTaylorDegree.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder.AuditTruncatedTaylorDegree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => x.natDegree) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditTruncatedTaylorDegree

end Reg.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
