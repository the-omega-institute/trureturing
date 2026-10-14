import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
open LeanInformationAudit Finset Polynomial Complex
open scoped BigOperators

universe u
noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder

namespace AuditLorentzReproduction
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun p => ℂ[X]) (fun _ => ℂ[X])
def actual : Realization signature :=
  realize signature (fun _ p x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ {m r : ℕ} (hm : 0 < m) (P : ℂ[X])
    (hdeg : P.natDegree ≤ r),
    lorentzOperator m r P = F.readout () () P
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 0 (by omega) 0 (by simp)
  have good := @lorentz_reproduction 1 0 (by omega) 0 (by simp)
  rw [good] at hh
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@lorentz_reproduction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lorentz_reproduction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lorentz_reproduction) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder.AuditLorentzReproduction.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder.AuditLorentzReproduction.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditLorentzReproduction

namespace AuditLowDegreeCoefficientRemainder
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun p => Fin (p+1) → ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (r : ℕ),
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d m : ℕ, 0 < d → d ≤ m → ∀ c : Fin (d+1) → ℂ,
      ∃ a : Fin (m+r+1) → ℂ,
        bernsteinRealization d c - lorentzOperator m r (bernsteinRealization d c) =
          bernsteinRealization (m+r) a ∧
        ‖a‖ ≤ K * ((d : ℝ)/m)^(((r : ℝ)+1)/2) * F.readout () d c ∧ (d ≤ r → a = 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K, hK, hb⟩ := h 0
  obtain ⟨a, he, ha, hz⟩ := hb 1 1 (by omega) (by omega) 0
  have hnonneg := norm_nonneg a
  norm_num [rejected, realize] at ha
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨0, 0, (fun _ => 1), by simp [actual, realize]⟩
def family : Registration arena (type_of% (@low_degree_coefficient_remainder)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@low_degree_coefficient_remainder, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@low_degree_coefficient_remainder) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder.AuditLowDegreeCoefficientRemainder.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder.AuditLowDegreeCoefficientRemainder.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditLowDegreeCoefficientRemainder

end Reg.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
