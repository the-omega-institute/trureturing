import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
open LeanInformationAudit Finset Polynomial Complex
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl

namespace AuditDeltaPositive
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p n => delta n p) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ {n : ℕ} (hn : 0 < n) (p : ℝ),
    0 < F.readout () p n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 (by omega) 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨0, 1, 2, by norm_num [actual, realize, delta]⟩
def family : Registration arena (type_of% (@delta_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@delta_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@delta_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditDeltaPositive.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditDeltaPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => delta n p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditDeltaPositive

namespace AuditInverseDeltaComparison
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ {m : ℕ} (hm : 0 < m) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1),
        delta m x / delta m y ≤ 1 + F.readout () () (x - y)/delta m x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 (by omega) 0 0 (by norm_num) (by norm_num)
  norm_num [rejected, realize, delta] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@inverse_delta_comparison)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverse_delta_comparison, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@inverse_delta_comparison) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditInverseDeltaComparison.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditInverseDeltaComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditInverseDeltaComparison

namespace AuditWeightedKernel
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (ℓ : ℕ) (γ : ℝ) (hγ : 0 ≤ γ),
        ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 0 < n → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ range (n + 1), |(i : ℝ)/(n : ℝ) - p| ^ γ *
        |(derivative^[ℓ] (bernsteinPolynomial ℝ n i)).eval p|) ≤
          F.readout () () K * delta n p ^ (γ - (ℓ : ℝ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K,hK,hb⟩ := h 0 0 (by norm_num)
  have hh := hb 1 (by omega) 0 (by norm_num)
  have hn : 0 ≤ ∑ i ∈ range (1 + 1), |(i : ℝ)/(1 : ℝ) - 0| ^ (0 : ℝ) *
      |(derivative^[0] (bernsteinPolynomial ℝ 1 i)).eval 0| :=
    sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _)
  simp only [rejected, realize, Nat.cast_zero, sub_self, Real.rpow_zero, mul_one] at hh hn
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@weighted_derivative_kernel_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_derivative_kernel_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_derivative_kernel_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditWeightedKernel.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditWeightedKernel.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditWeightedKernel

namespace AuditHolderDerivative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (r : ℕ) (β : ℝ) (hβ : (r : ℝ) < β),
        ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℂ), ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) y‖ ≤ A * |x - y| ^ (β - (r : ℝ))) →
      ∀ m : ℕ, 0 < m → ∀ p ∈ Set.Icc (0 : ℝ) 1,
        (∀ j ≤ r, ‖iteratedDerivWithin j f (Set.Icc (0 : ℝ) 1) p -
          (derivative^[j] (holderOperator m r f)).eval (p : ℂ)‖ ≤
            K * A * delta m p ^ (β - (j : ℝ))) ∧
        F.readout () () ((derivative^[r + 1] (holderOperator m r f)).eval (p : ℂ)) ≤
          K * A * delta m p ^ (β - ((r + 1 : ℕ) : ℝ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K,hK,hb⟩ := h 0 1 (by norm_num)
  have hh := (hb (fun _ => 0) contDiffOn_const 0 (by norm_num)
    (by intro x hx y hy; simp) 1 (by omega) 0 (by norm_num)).2
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@holder_derivative_control)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@holder_derivative_control, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@holder_derivative_control) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditHolderDerivative.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditHolderDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditHolderDerivative

namespace AuditHolderSeminorm
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (r : ℕ) (β : ℝ) (hβ : (r : ℝ) < β)
    (hβ1 : β < (r : ℝ) + 1),
        ∃ L : ℝ, 0 < L ∧ ∀ (f : ℝ → ℂ), ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r f (Set.Icc (0 : ℝ) 1) y‖ ≤ A * |x - y| ^ (β - (r : ℝ))) →
      ∀ m : ℕ, 0 < m → ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        F.readout () () ((derivative^[r] (holderOperator m r f)).eval (x : ℂ) -
          (derivative^[r] (holderOperator m r f)).eval (y : ℂ)) ≤
            L * A * |x - y| ^ (β - (r : ℝ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨L,hL,hb⟩ := h 0 (1/2) (by norm_num) (by norm_num)
  have hh := hb (fun _ => 0) contDiffOn_const 0 (by norm_num)
    (by intro x hx y hy; simp) 1 (by omega) 0 (by norm_num) 0 (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@holder_seminorm_control)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@holder_seminorm_control, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@holder_seminorm_control) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditHolderSeminorm.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditHolderSeminorm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditHolderSeminorm

namespace AuditWeightedStability
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (r : ℕ) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1),
        ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m → ∀ A : ℝ, 0 ≤ A → ∀ V : ℂ[X],
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖(derivative^[r + 1] V).eval (x : ℂ)‖ ≤ A * delta m x ^ (-e)) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        F.readout () () ((derivative^[r + 1] (lorentzOperator m r V)).eval (p : ℂ)) ≤ K * A * delta m p ^ (-e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K,hK,hb⟩ := h 0 0 (by norm_num) (by norm_num)
  have hh := hb 1 (by omega) 0 (by norm_num) 0
    (by intro x hx; simp) 0 (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@weighted_lorentz_stability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_lorentz_stability, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_lorentz_stability) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditWeightedStability.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl.AuditWeightedStability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditWeightedStability

end Reg.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
