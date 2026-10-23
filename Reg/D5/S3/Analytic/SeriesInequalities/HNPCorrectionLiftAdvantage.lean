import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
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
open _root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets
open LeanInformationAudit Finset Polynomial Complex Filter
open scoped BigOperators Topology ContDiff
universe u v
noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage

namespace AuditCorrectionUniformBound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {n r t : ℕ} {ρ θ : ℝ}
    (hn : 0 < n) (hr : r ≤ n) (ht : t ≤ n+r) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ),
    lift (n+r) n t (correction ρ θ n) ≤ ((R.readout () () θ)+1)*(n : ℝ)^(-ρ/2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 0 0 0 0 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
  norm_num [rejected, realize, _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.lift, weight, correction, sample, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_uniform_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_uniform_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.correction_uniform_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditCorrectionUniformBound.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditCorrectionUniformBound.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
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
end AuditCorrectionUniformBound

namespace AuditUniformRingCorrectionBudget
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℕ) (ρ θ : ℝ)
    (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ),
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar A H ε : ℝ, 0 < xstar → 0 ≤ A → 0 ≤ H → 0 < ε →
      ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ j : ℕ,
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ c : ℂ, ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x-c‖ ≤ M) →
      (∀ ν ∈ Icc 1 r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin ν f (Set.Icc 0 1) x‖ ≤
          A*(ringScale xstar b j)^(-(ν : ℝ))) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤
            H*(ringScale xstar b j)^(-ρ)*|x-y|^(ρ-(r : ℝ))) →
      ∀ k : ℕ,
        (∀ t ≤ (N*b^j)*b^k+r,
          ‖bernsteinCoefficient ((N*b^j)*b^k+r) t (center (N*b^j) b r f k)-c‖ +
            D*(ringScale xstar b j)^(-ρ)*
              lift ((N*b^j)*b^k+r) ((N*b^j)*b^k) t
                (correction ρ θ ((N*b^j)*b^k)) ≤ M+(R.readout () () ε)) ∧
        (∀ t ≤ (N*b^j)*b^(k+1)+r,
          ‖bernsteinCoefficient ((N*b^j)*b^(k+1)+r) t
            (center (N*b^j) b r f (k+1)-center (N*b^j) b r f k)‖ ≤
            D*(ringScale xstar b j)^(-ρ)*
              (lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t
                (fun i => lift ((N*b^j)*b^k+r) ((N*b^j)*b^k) i
                  (correction ρ θ ((N*b^j)*b^k))) -
               lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^(k+1)) t
                (correction ρ θ ((N*b^j)*b^(k+1)))))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B,hB,hb⟩ := h 2 (5/2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨D,hD,N,hN,hc⟩ := hb B le_rfl 1 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hh := (hc 0 (fun _ => 0) contDiffOn_const 0 0 (by norm_num)
    (by intro x hx; simp) (by intro nu hnu x hx; simp [iteratedDerivWithin_const])
    (by intro x hx y hy; simp [iteratedDerivWithin_const]) 0).1 0 (by omega)
  have hn : 0 < N := by omega
  have hcpos := correction_lift_pos (N := N+2) (K := N) (t := 0) (ρ := (5/2 : ℝ))
    (θ := 1) (by omega) (by omega) hn (by norm_num)
  norm_num [rejected, realize, ringScale] at hh
  nlinarith [norm_nonneg (bernsteinCoefficient (N+2) 0 (center N B 2 (fun _ => 0) 0))]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.uniform_ring_correction_budget)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.uniform_ring_correction_budget, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.uniform_ring_correction_budget) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditUniformRingCorrectionBudget.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditUniformRingCorrectionBudget.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditUniformRingCorrectionBudget

namespace AuditFullQxJetEq
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (φ : ℝ → ℝ) (η a b : ℝ) (m ell : ℕ) (x q : ℝ),
    fullQxJet φ η a b m ell x q =
      qxJet (R.readout () () φ) η a b m ell x q + if m = 0 ∧ ell = 0 then 1 / 2 else 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 0) 1 0 0 0 0 1 0
  norm_num [rejected, realize, fullQxJet, qxJet, reference] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.fullQxJet_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.fullQxJet_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.fullQxJet_eq) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditFullQxJetEq.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditFullQxJetEq.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn", "fn", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditFullQxJetEq

namespace AuditProfileSmooth
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (abs : ℝ → ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k m : ℕ),
    ContDiff ℝ ∞ (profile (R.readout () () φ) k m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) contDiff_const 0 0
  have hd : ContDiff ℝ ∞ (abs : ℝ → ℝ) := by simpa [rejected, realize, profile] using hh
  exact not_differentiableAt_abs_zero ((hd.differentiable (by simp)) 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.profile_smooth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.profile_smooth, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.profile_smooth) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditProfileSmooth.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditProfileSmooth.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditProfileSmooth

namespace AuditProfileCompact
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {φ : ℝ → ℝ} (hφ : HasCompactSupport φ) (k m : ℕ),
    HasCompactSupport (profile (R.readout () () φ) k m)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) HasCompactSupport.zero 0 0
  have hc : IsCompact (Set.univ : Set ℝ) := by
    simpa [rejected, realize, profile, HasCompactSupport, tsupport, Function.support] using hh
  exact not_bddAbove_univ hc.bddAbove
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.profile_compact)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.profile_compact, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.profile_compact) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditProfileCompact.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditProfileCompact.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditProfileCompact

namespace AuditIteratedSmooth
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (abs : ℝ → ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (ell : ℕ),
    ContDiff ℝ ∞ (iteratedDeriv ell (R.readout () () φ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) contDiff_const 0
  have hd : ContDiff ℝ ∞ (abs : ℝ → ℝ) := by simpa [rejected, realize] using hh
  exact not_differentiableAt_abs_zero ((hd.differentiable (by simp)) 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.iterated_smooth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.iterated_smooth, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.iterated_smooth) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditIteratedSmooth.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditIteratedSmooth.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditIteratedSmooth

namespace AuditAffineIterated
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ell : ℕ) (a b x q : ℝ),
    iteratedDeriv ell (fun u => φ ((a + b * u) / x)) q =
      b ^ ell * x ^ (-(ell : ℤ)) * iteratedDeriv ell (R.readout () () φ) ((a + b * q) / x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) contDiff_const 0 0 0 1 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.affine_iterated)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.affine_iterated, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.affine_iterated) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditAffineIterated.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditAffineIterated.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditAffineIterated

namespace AuditXqFormula
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a b : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ),
    xqJet φ η a b m ell x q =
      η * b ^ ell * x ^ (-((ell + m : ℕ) : ℤ)) *
        profile (iteratedDeriv ell (R.readout () () φ)) ell m ((a + b * q) / x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) contDiff_const 1 0 0 0 0 1 (by norm_num) 0
  norm_num [rejected, realize, xqJet, reference, profile] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.xq_formula)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.xq_formula, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.xq_formula) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditXqFormula.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditXqFormula.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditXqFormula

namespace AuditQxFormula
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a b : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ),
    qxJet φ η a b m ell x q =
      η * b ^ ell * x ^ (-((m + ell : ℕ) : ℤ)) *
        iteratedDeriv ell (profile (R.readout () () φ) 0 m) ((a + b * q) / x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) contDiff_const 1 0 0 0 0 1 (by norm_num) 0
  norm_num [rejected, realize, qxJet, reference, profile] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.qx_formula)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.qx_formula, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.qx_formula) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditQxFormula.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditQxFormula.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditQxFormula

namespace AuditCutoffSmooth
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (abs : ℝ → ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Set.Ioi 0) (β : ℝ),
    ContDiff ℝ ∞ (cutoff (R.readout () () χ) β)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) contDiff_const
    (by change tsupport (0 : ℝ → ℝ) ⊆ _; simp only [tsupport_zero, Set.empty_subset]) 0
  have hz : ContDiff ℝ ∞ (fun x : ℝ => 2 * cutoff abs 0 x - x) :=
    (contDiff_const.mul hh).sub contDiff_id
  have he : (fun x : ℝ => 2 * cutoff abs 0 x - x) = abs := by
    funext x
    by_cases hx : 0 < x
    · simp [_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff,
        hx, abs_of_pos hx]
      ring
    · simp [_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff,
        hx, abs_of_nonpos (not_lt.mp hx)]
  rw [he] at hz
  exact not_differentiableAt_abs_zero ((hz.differentiable (by simp)) 0)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff_smooth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff_smooth, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff_smooth) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditCutoffSmooth.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditCutoffSmooth.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCutoffSmooth

namespace AuditCutoffReferenceMixedScales
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Set.Ioi 0)
    (β η a b c : ℝ) (hc : 0 < c),
    (∀ m ell : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ s x : ℝ, 0 < s → 0 < x → s / c ≤ x →
      ∀ q : ℝ,
        |xqJet (cutoff χ β) η a b m ell x q| ≤ K * s ^ (-((m + ell : ℕ) : ℝ)) ∧
        |qxJet (cutoff χ β) η a b m ell x q| ≤ K * s ^ (-((m + ell : ℕ) : ℝ))) ∧
    (∀ (m r : ℕ) (α : ℝ), 0 < α → α ≤ 1 → ∃ K : ℝ, 0 < K ∧
      ∀ s x : ℝ, 0 < s → 0 < x → x ≤ 1 → s / c ≤ x →
        (∀ ell ≤ r, ∀ q : ℝ,
          |fullQxJet (cutoff χ β) η a b m ell x q| ≤
            K * s ^ (-((m + r : ℕ) : ℝ) - α)) ∧
        (∀ q q' : ℝ,
          |fullQxJet (cutoff χ β) η a b m r x q - fullQxJet (cutoff χ β) η a b m r x q'| ≤
            (R.readout () () K) * s ^ (-((m + r : ℕ) : ℝ) - α) * |q - q'| ^ α))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := @h (fun _ => 0) contDiff_const HasCompactSupport.zero
    (by change tsupport (0 : ℝ → ℝ) ⊆ _; simp only [tsupport_zero, Set.empty_subset])
    0 0 0 0 1 (by norm_num)
  obtain ⟨K,hK,hb⟩ := hc.2 0 0 1 (by norm_num) (by norm_num)
  have hh := (hb 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 0 1
  norm_num [rejected, realize] at hh
  exact (not_lt_of_ge (abs_nonneg _)) (lt_of_le_of_lt hh (by norm_num))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff_reference_mixed_scales)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff_reference_mixed_scales, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.cutoff_reference_mixed_scales) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditCutoffReferenceMixedScales.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditCutoffReferenceMixedScales.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCutoffReferenceMixedScales

namespace AuditComplexJet
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (ν : ℕ)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1),
    iteratedDerivWithin ν (fun q => (f q : ℂ)) (Set.Icc 0 1) q =
      ((iteratedDeriv ν (R.readout () () f) q : ℝ) : ℂ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h (fun _ => 0) contDiff_const 0 0 (by norm_num)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.complex_jet)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.complex_jet, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.complex_jet) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditComplexJet.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditComplexJet.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditComplexJet

namespace AuditReferenceRingEnvelopes
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x / 20) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ),
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar : ℝ, 0 < xstar → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ j : ℕ, ∀ x : ℝ,
      0 < x → x ≤ 1 → ringScale xstar b j / Real.sqrt b ≤ x →
      let f := fun q : ℝ => (reference (cutoff χ β) (2/(5*T^β)) a d x q : ℂ)
      let lower := ringLower (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ)) f
      let upper := ringUpper (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ)) f
      ∀ k : ℕ,
        (∀ t ≤ (N*b^j)*b^k+r, (9/20 : ℝ) ≤ lower k t ∧
          lower k t ≤ upper k t ∧ upper k t ≤ (R.readout () () 19)) ∧
        (∀ t ≤ (N*b^j)*b^(k+1)+r,
          lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t (lower k) ≤ lower (k+1) t ∧
          upper (k+1) t ≤ lift ((N*b^j)*b^(k+1)+r) ((N*b^j)*b^k+r) t (upper k))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B,hB,hb⟩ := @h (fun _ => 0) contDiff_const HasCompactSupport.zero 1 0
    (by norm_num) (by norm_num)
    (by change tsupport (0 : ℝ → ℝ) ⊆ _; simp only [tsupport_zero, Set.empty_subset])
    (by intro t; norm_num) 0 0 2 (5/2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨D,hD,N,hN,hc⟩ := hb B le_rfl 1 (by norm_num)
  have hs : 1 / Real.sqrt (B : ℝ) ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.2 (by positivity))).2
    exact Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ B by omega))
  have hh := (hc 0 1 (by norm_num) (by norm_num) (by simpa [ringScale] using hs) 0).1 0 (by omega)
  norm_num [rejected, realize] at hh
  linarith [hh.1, hh.2.1, hh.2.2]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 20, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.reference_ring_envelopes)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.reference_ring_envelopes, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ReferenceProfileMixedJets.reference_ring_envelopes) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditReferenceRingEnvelopes.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.AuditReferenceRingEnvelopes.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x / 20) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditReferenceRingEnvelopes

end Reg.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
