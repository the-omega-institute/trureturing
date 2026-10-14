import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.Calculus.Deriv.Abs

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzLocalCoefficientKernel
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzCoefficientRemainder
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
open _root_.D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability
open _root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
open _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
open LeanInformationAudit Finset Polynomial Complex Filter
open scoped BigOperators Topology ContDiff
universe u v
noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale

namespace AuditResidualCoefficientControl
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (ρ : ℝ) (hρ : (r : ℝ) < ρ),
    ∃ K : ℝ, 0 < K ∧ ∀ n b : ℕ, 0 < n → r ≤ n*b → 1 ≤ b →
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ P : ℂ[X], ∀ A : ℝ, 0 ≤ A →
      (∀ ν ≤ r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x -
          (derivative^[ν] P).eval (x : ℂ)‖ ≤ A * delta n x ^ (ρ - (ν : ℝ))) →
      ∀ J ≤ n*b+r,
        ‖bernsteinCoefficient (n*b+r) J
          (holderOperator (n*b) r (fun x : ℝ => f x - P.eval (x : ℂ)))‖ ≤
            (R.readout () () K) * A * ((b : ℝ)*((r : ℝ)+1))^ρ *
              delta (n*b) ((J : ℝ)/(n*b+r))^ρ
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K,hK,hb⟩ := h 0 (1/2) (by norm_num)
  have hh := hb 1 1 (by omega) (by omega) (by omega) (fun _ => 0) contDiffOn_const
    0 1 (by norm_num) (by
      intro nu hnu x hx
      have hn : nu = 0 := by omega
      subst nu
      simpa using Real.rpow_nonneg (le_of_lt (delta_pos (by omega : 0 < 1) x)) (1/2)) 0 (by omega)
  norm_num [rejected, realize, delta] at hh
  exact (not_lt_of_ge (norm_nonneg _)) (lt_of_le_of_lt hh (by norm_num))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.residual_coefficient_control)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.residual_coefficient_control, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.residual_coefficient_control) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditResidualCoefficientControl.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditResidualCoefficientControl.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditResidualCoefficientControl

namespace AuditDeltaUpper
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1),
    delta n x ≤ ((R.readout () () n) : ℝ)^(-(1/2 : ℝ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 (by omega) 0 (by norm_num)
  norm_num [rejected, realize, delta, Real.zero_rpow] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.delta_upper)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.delta_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.delta_upper) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditDeltaUpper.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditDeltaUpper.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditDeltaUpper

namespace AuditCenterCoefficientControl
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (ρ : ℝ)
    (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1),
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b → ∃ K : ℝ, 0 < K ∧
      ∀ τ : ℕ, 0 < τ → r ≤ τ → ∀ f : ℝ → ℂ,
      ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ c : ℂ, ∀ M A H s : ℝ, 0 ≤ M → 0 ≤ A → 0 ≤ H → 0 < s →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x-c‖ ≤ M) →
      (∀ ν ∈ Icc 1 r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x‖ ≤ A*s^(-(ν : ℝ))) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤ H*|x-y|^(ρ-(r : ℝ))) →
      ∀ k : ℕ, ∀ J ≤ τ*b^k+r,
        ‖bernsteinCoefficient (τ*b^k+r) J (center τ b r f k)-c‖ ≤
          M + K*A*(∑ ν ∈ Icc 1 r, (τ : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ))) +
            (R.readout () () K)*H*(τ : ℝ)^(-ρ/2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B,hB,hb⟩ := h 0 (1/2) (by norm_num) (by norm_num)
  obtain ⟨K,hK,hc⟩ := hb B le_rfl
  have hh := hc 1 (by omega) (by omega) (fun _ => 0) contDiffOn_const
    0 0 0 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro x hx; simp <;> positivity) (by intro nu hnu; norm_num at hnu)
    (by intro x hx y hy; simp <;> positivity) 0 0 (by simp)
  norm_num [rejected, realize] at hh
  exact (not_lt_of_ge (norm_nonneg _)) (lt_of_le_of_lt hh (by norm_num))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.center_coefficient_control)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.center_coefficient_control, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.center_coefficient_control) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCenterCoefficientControl.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCenterCoefficientControl.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCenterCoefficientControl

namespace AuditRingScaleCancel
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
    {xstar : ℝ} (hx : 0 < xstar) (j : ℕ) (e : ℝ),
    ((N*b^j : ℕ) : ℝ)^(-e/2)*(ringScale xstar b j)^(-e) =
      (N : ℝ)^(-e/2)*(R.readout () () xstar)^(-e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 1 (by omega) (by omega) 1 (by norm_num) 0 1
  norm_num [rejected, realize, ringScale, Real.zero_rpow] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.ring_scale_cancel)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.ring_scale_cancel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.ring_scale_cancel) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditRingScaleCancel.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditRingScaleCancel.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditRingScaleCancel

namespace AuditUniformRingCenterMargin
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (ρ : ℝ)
    (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1),
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar A H ε : ℝ, 0 < xstar → 0 ≤ A → 0 ≤ H → 0 < ε →
      ∃ N : ℕ, 3*r+1 ≤ N ∧ ∀ j : ℕ,
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ c : ℂ, ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x-c‖ ≤ M) →
      (∀ ν ∈ Icc 1 r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x‖ ≤ A*(ringScale xstar b j)^(-(ν : ℝ))) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤
            H*(ringScale xstar b j)^(-ρ)*|x-y|^(ρ-(r : ℝ))) →
      ∀ k : ℕ, ∀ J ≤ (N*b^j)*b^k+r,
        ‖bernsteinCoefficient ((N*b^j)*b^k+r) J (center (N*b^j) b r f k)-c‖ ≤ M+(R.readout () () ε)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B,hB,hb⟩ := h 0 (1/2) (by norm_num) (by norm_num)
  obtain ⟨N,hN,hc⟩ := hb B le_rfl 1 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hh := hc 0 (fun _ => 0) contDiffOn_const 0 0 (by norm_num)
    (by intro x hx; simp <;> positivity) (by intro nu hnu; norm_num at hnu) (by intro x hx y hy; simp <;> positivity)
    0 0 (by omega)
  norm_num [rejected, realize] at hh
  exact (not_lt_of_ge (norm_nonneg _)) (lt_of_le_of_lt hh (by norm_num))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.uniform_ring_center_margin)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.uniform_ring_center_margin, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.uniform_ring_center_margin) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditUniformRingCenterMargin.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditUniformRingCenterMargin.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditUniformRingCenterMargin

namespace AuditWeightSum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N),
    ∑ k ∈ range ((R.readout () () n) + 1), weight N K n k = 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 1 1 (by omega) (by omega)
  norm_num [rejected, realize, weight, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.weight_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.weight_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.weight_sum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditWeightSum.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditWeightSum.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditWeightSum

namespace AuditCorrectionLiftLower
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N K n : ℕ} {ρ θ : ℝ}
    (hK : K ≤ N) (hn : n ≤ N) (hK2 : 2 ≤ K) (hρ : 2 ≤ ρ),
    (R.readout () () θ) / (K : ℝ) ^ ρ +
      (((n : ℝ) / N * (1 - (n : ℝ) / N)) / (2 * K)) ^ (ρ / 2) ≤
      lift N K n (correction ρ θ K)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 2 2 2 2 0 (by omega) (by omega) (by omega) (by norm_num)
  norm_num [rejected, realize, _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.lift, weight, correction, sample, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_lower)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_lower) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftLower.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftLower.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCorrectionLiftLower

namespace AuditCorrectionLiftUpper
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N K n : ℕ} {ρ θ : ℝ}
    (hK : K ≤ N) (hn : n ≤ N) (hKpos : 0 < K) (hNK : N ≤ 2 * K)
    (hρ : 0 ≤ ρ),
    lift N K n (correction ρ θ K) ≤
      (R.readout () () θ) / (K : ℝ) ^ ρ +
        (4 * ((n : ℝ) / N * (1 - (n : ℝ) / N)) / K) ^ (ρ / 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 1 1 0 0 (by omega) (by omega) (by omega) (by omega) (by norm_num)
  norm_num [rejected, realize, _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.lift, weight, correction, sample, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_upper)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_upper) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftUpper.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftUpper.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCorrectionLiftUpper

namespace AuditCorrectionLiftPos
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N K t : ℕ} {ρ θ : ℝ}
    (hK : K ≤ N) (ht : t ≤ N) (hK0 : 0 < K) (hθ : 0 < θ),
    0 < lift N K t (correction ρ (R.readout () () θ) K)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 1 1 2 1 (by omega) (by omega) (by omega) (by norm_num)
  norm_num [rejected, realize, _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.lift, weight, correction, sample, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_pos) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftPos.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftPos.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCorrectionLiftPos

namespace AuditCorrectionLiftAdvantage
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n m r t : ℕ} {ρ θ : ℝ}
    (hn : 2 ≤ n) (hm : 16 * n ≤ m) (hr : r ≤ m) (ht : t ≤ m + r)
    (hρ : 2 ≤ ρ) (hθ : 0 ≤ θ),
    (2 * lift (m + r) m t (correction ρ θ m) ≤
      lift (m + r) (n + r) t (fun i => lift (n + r) n i (correction ρ (R.readout () () θ) n))) ∧
    (0 < θ → lift (m + r) m t (correction ρ θ m) <
      lift (m + r) (n + r) t (fun i => lift (n + r) n i (correction ρ θ n)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (@h 2 32 0 0 2 0 (by omega) (by omega) (by omega) (by omega)
    (by norm_num) (by norm_num)).1
  norm_num [rejected, realize, _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.lift,
    weight, correction, sample, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_advantage)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_advantage, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_lift_advantage) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftAdvantage.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale.AuditCorrectionLiftAdvantage.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCorrectionLiftAdvantage

end Reg.D5.S3.Analytic.SeriesInequalities.OriginalRingEnvelopeScale
