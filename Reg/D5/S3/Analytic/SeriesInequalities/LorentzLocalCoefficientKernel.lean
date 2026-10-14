import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel

open LeanInformationAudit Finset Polynomial Complex
open scoped BigOperators

universe u
noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel

namespace AuditCentralZero
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (m : ℕ),
    F.readout () () (centralMoment m 0) = 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@central_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@central_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@central_zero) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditCentralZero.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditCentralZero.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCentralZero

namespace AuditTauDegree
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ p x => x.natDegree) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (m n : ℕ),
    F.readout () () (tau m n) ≤ n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, X, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@tau_degree)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tau_degree, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tau_degree) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditTauDegree.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditTauDegree.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
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
end AuditTauDegree

namespace AuditTauCoefficientBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (n : ℕ),
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, 0 < m → ∀ h : ℕ, h ≤ n →
      F.readout () () (bernsteinCoefficient n h (C (((m : ℂ)^n)⁻¹) * tau m n)) ≤
        K * min ((m : ℝ)^h / (m : ℝ)^n) ((m : ℝ)^(n-h) / (m : ℝ)^n)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K, hK, hb⟩ := h 1
  obtain ⟨m, hm⟩ := exists_nat_gt K
  have hmpos : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hh := hb m hmpos 0 (by omega)
  simp only [rejected, realize, pow_zero, pow_one, tsub_zero] at hh
  have hsmall : K * min (1 / (m : ℝ)) ((m : ℝ) / m) ≤ K / m := by
    calc
      _ ≤ K * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
      _ = _ := by ring
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hh' := (le_div_iff₀ hmR).mp (hh.trans hsmall)
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@tau_coefficient_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tau_coefficient_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tau_coefficient_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditTauCoefficientBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditTauCoefficientBound.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditTauCoefficientBound

namespace AuditWeightedTauBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (n : ℕ),
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m D J : ℕ, 0 < m → 0 < D → 2*n ≤ D → J ≤ D →
      (∑ h ∈ range (n+1), samplingWeight D J n h *
        F.readout () () (bernsteinCoefficient n h (C (((m : ℂ)^n)⁻¹) * tau m n))) ≤
          K * (derivativeRadius m 1 ((J : ℝ)/D))^n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K, hK, hb⟩ := h 1
  obtain ⟨m, hm⟩ := exists_nat_gt K
  have hmpos : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have hh := hb m 2 0 hmpos (by omega) (by omega) (by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  norm_num [rejected, realize, samplingWeight, derivativeRadius,
    Finset.sum_range_succ, max_eq_right (by positivity : (0 : ℝ) ≤ 1 / m)] at hh
  have hh' := (le_div_iff₀ hmR).mp (show 1 ≤ K / (m : ℝ) by simpa only [div_eq_mul_inv] using hh)
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@weighted_tau_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_tau_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_tau_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditWeightedTauBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditWeightedTauBound.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditWeightedTauBound

namespace AuditBasisTimesLocalBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ {m r n J h : ℕ} (hn : n ≤ r) (hh : h ≤ n)
    (hJ : J ≤ m+r) (f : ℕ → ℂ) {M : ℝ}
    (hf : ∀ i : ℕ, i ≤ m → i ≤ J → J ≤ i+r → ‖f i‖ ≤ M),
    F.readout () () (bernsteinCoefficient (m+r) J (bernsteinPolynomial ℂ n h *
      ∑ i ∈ range (m+1), C (f i) * bernsteinPolynomial ℂ m i)) ≤
        M * samplingWeight (m+r) J n h
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 0 0 0 0 (by omega) (by omega) (by omega) (fun _ => 0) 0 (by simp)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@basis_times_local_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@basis_times_local_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_times_local_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditBasisTimesLocalBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditBasisTimesLocalBound.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
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
end AuditBasisTimesLocalBound

namespace AuditLocalCoefficientBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (r : ℕ),
    ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, 0 < m → r ≤ m → ∀ J : ℕ, J ≤ m+r →
      ∀ A : ℝ, 0 ≤ A → ∀ f : ℕ → ℕ → ℂ,
      (∀ ν : ℕ, ν ≤ r → ∀ i : ℕ, i ≤ m → i ≤ J → J ≤ i+r →
        ‖f ν i‖ ≤ A / (derivativeRadius m 1 ((J : ℝ)/(m+r)))^ν) →
      F.readout () () (bernsteinCoefficient (m+r) J (lorentzJet m r f)) ≤ K*A
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K, hK, hb⟩ := h 0
  have hh := hb 1 (by omega) (by omega) 0 (by omega) 0 (by norm_num) (fun _ _ => 0) (by simp)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@local_coefficient_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_coefficient_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@local_coefficient_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditLocalCoefficientBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel.AuditLocalCoefficientBound.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditLocalCoefficientBound

end Reg.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
