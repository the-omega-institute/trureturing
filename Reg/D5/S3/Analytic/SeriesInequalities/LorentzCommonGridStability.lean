import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.Calculus.Deriv.Abs

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability

open LeanInformationAudit Finset Polynomial Complex Filter
open scoped BigOperators Topology ContDiff
universe u v
noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability

namespace AuditResidualJet
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℝ → ℂ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {r j : ℕ} (hj : j ≤ r) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1)) (P : ℂ[X]) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1),
    iteratedDerivWithin j (fun y : ℝ => f y - P.eval (y : ℂ)) (Set.Icc 0 1) x =
      iteratedDerivWithin j (R.readout () () f) (Set.Icc 0 1) x - (derivative^[j] P).eval (x : ℂ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 0 (by omega) (fun _ => 0) contDiffOn_const 0 0 (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.residual_jet)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.residual_jet, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.residual_jet) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.AuditResidualJet.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.AuditResidualJet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditResidualJet

namespace AuditOperatorResidual
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℝ → ℂ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {m r : ℕ} (hm : 0 < m) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1)) (P : ℂ[X]),
    holderOperator m r (fun x : ℝ => f x - P.eval (x : ℂ)) =
      holderOperator m r (R.readout () () f) - lorentzOperator m r P
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 0 (by omega) (fun _ => 0) contDiffOn_const 0
  norm_num [rejected, realize, holderOperator, lorentzOperator, lorentzJet,
    tau, centralMoment, bernsteinPolynomial, samplingWeight, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.operator_residual)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.operator_residual, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.operator_residual) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.AuditOperatorResidual.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.AuditOperatorResidual.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditOperatorResidual

namespace AuditCommonGridStability
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (β : ℝ) (hβ : (r : ℝ) < β)
    (hβ1 : β < (r : ℝ) + 1),
    ∃ B : ℕ, 2 ≤ B ∧ ∃ U V E : ℝ, 0 < U ∧ 0 < V ∧ 0 < E ∧
      ∀ b : ℕ, B ≤ b → ∀ τ : ℕ, 0 < τ →
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ H : ℝ, 0 ≤ H →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤ H * |x - y| ^ (β - (r : ℝ))) →
      ∀ j : ℕ,
        (center τ b r f j).natDegree ≤ τ * b ^ j + r ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
          ‖(derivative^[r] (center τ b r f j)).eval (x : ℂ)-
            (derivative^[r] (center τ b r f j)).eval (y : ℂ)‖ ≤
              U * H * |x - y| ^ (β - (r : ℝ))) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖(derivative^[r + 1] (center τ b r f j)).eval (x : ℂ)‖ ≤
            V * H * delta (τ * b ^ j) x ^ (-((r : ℝ) + 1 - β))) ∧
        ∀ ν ≤ r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedDerivWithin ν f (Set.Icc 0 1) x-
            (derivative^[ν] (center τ b r f j)).eval (x : ℂ)‖ ≤
              (R.readout () () E) * H * delta (τ * b ^ j) x ^ (β - (ν : ℝ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B,hB,U,V,E,hU,hV,hE,hb⟩ := h 0 (1/2) (by norm_num) (by norm_num)
  have hh := (hb B le_rfl 1 (by omega) (fun _ => 0) contDiffOn_const 1 (by norm_num)
    (by intro x hx y hy; simp <;> positivity) 0).2.2.2 0 (by omega) 0 (by norm_num)
  norm_num [rejected, realize, delta] at hh
  exact (not_lt_of_ge (norm_nonneg _)) (lt_of_le_of_lt hh (by norm_num))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.common_grid_stability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.common_grid_stability, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.common_grid_stability) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.AuditCommonGridStability.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability.AuditCommonGridStability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCommonGridStability

end Reg.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability
