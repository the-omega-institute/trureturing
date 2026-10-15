import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
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
open _root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
open LeanInformationAudit Finset Polynomial Complex Filter
open scoped BigOperators Topology ContDiff
universe u v
noncomputable section
namespace Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport

namespace AuditLinearIterated
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {f : ℝ → E} {x : ℝ} {m : ℕ} (hf : ContDiffAt ℝ m f x),
    iteratedDeriv m (fun y => L (f y)) x = L (iteratedDeriv (R.readout () () m) f x)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let upE : ℝ →L[ℝ] ULift.{u} ℝ :=
    (ContinuousLinearEquiv.ulift : ULift.{u} ℝ ≃L[ℝ] ℝ).symm.toContinuousLinearMap
  let upF : ℝ →L[ℝ] ULift.{v} ℝ :=
    (ContinuousLinearEquiv.ulift : ULift.{v} ℝ ≃L[ℝ] ℝ).symm.toContinuousLinearMap
  let downE : ULift.{u} ℝ →L[ℝ] ℝ :=
    (ContinuousLinearEquiv.ulift : ULift.{u} ℝ ≃L[ℝ] ℝ).toContinuousLinearMap
  let L := upF.comp downE
  have hh := @h (ULift.{u} ℝ) (ULift.{v} ℝ) inferInstance inferInstance
    inferInstance inferInstance L upE 0 1 upE.contDiff.contDiffAt
  have he : (fun y : ℝ => L (upE y)) = upF := rfl
  rw [he, iteratedDeriv_one, ContinuousLinearMap.deriv] at hh
  have heq := congrArg ULift.down hh
  norm_num [rejected, realize, upF, L, downE, upE, ContinuousLinearEquiv.ulift] at heq
  change (1 : ℝ) = 0 at heq
  norm_num at heq
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.linear_iterated)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.linear_iterated, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.linear_iterated) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditLinearIterated.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditLinearIterated.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditLinearIterated

namespace AuditReferenceTransport
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (fun _ => 1)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (η a d : ℝ) (r k D J m : ℕ)
    {x : ℝ} (hx : 0 < x),
    iteratedDeriv m (fun y => bernsteinCoefficient D J
      (center τ b r (fun q : ℝ => (reference φ η a d y q : ℂ)) k)) x =
        bernsteinCoefficient D J (center τ b r
          (fun q : ℝ => ((iteratedDeriv m (fun y => reference (R.readout () () φ) η a d y q) x : ℝ) : ℂ)) k)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 1 (by omega) (by omega) (fun _ => 0) contDiff_const
    1 0 0 0 0 1 0 0 1 (by norm_num)
  norm_num [rejected, realize, reference, center, holderOperator, lorentzJet,
    tau, bernsteinPolynomial, bernsteinCoefficient, Finset.sum_range_succ] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_transport)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_transport, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_transport) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditReferenceTransport.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditReferenceTransport.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "arg", "fn", "arg", "body", "fn", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditReferenceTransport

namespace AuditReferenceCenterMixedScales
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Set.Ioi 0)
    (β η a d : ℝ) (r : ℕ) (ρ : ℝ) (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1),
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar : ℝ, 0 < xstar → ∀ N : ℕ, r+1 ≤ N →
      ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ x : ℝ,
      0 < x → x ≤ 1 → ringScale xstar b j / Real.sqrt b ≤ x →
      let f := fun y q : ℝ => (reference (cutoff χ β) η a d y q : ℂ)
      let fm := fun q : ℝ => ((iteratedDeriv m
        (fun y => reference (cutoff χ β) η a d y q) x : ℝ) : ℂ)
      ∀ k : ℕ,
        (∀ t ≤ (N*b^j)*b^k+r,
          ‖iteratedDeriv m (fun y => bernsteinCoefficient ((N*b^j)*b^k+r) t
            (center (N*b^j) b r (f y) k)) x‖ ≤ C*(ringScale xstar b j)^(-(m : ℝ))) ∧
        (∀ t ≤ (N*b^j)*b^(k+1)+r,
          ‖iteratedDeriv m (fun y => bernsteinCoefficient ((N*b^j)*b^(k+1)+r) t
            (center (N*b^j) b r (f y) (k+1)-center (N*b^j) b r (f y) k)) x‖ ≤
              C*(ringScale xstar b j)^(-(m : ℝ)-ρ)*
                (((N*b^j)*b^(k+1) : ℕ) : ℝ)^(-ρ/2)) ∧
        (∀ ell ≤ r, ∀ q ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedDerivWithin ell fm (Set.Icc 0 1) q -
            (derivative^[ell] (center (N*b^j) b r fm k)).eval (q : ℂ)‖ ≤
              (R.readout () () C)*(ringScale xstar b j)^(-(m : ℝ)-ρ)*
                delta ((N*b^j)*b^k) q^(ρ-(ell : ℝ)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B,hB,hb⟩ := @h (fun _ => 0) contDiff_const HasCompactSupport.zero (by change tsupport (0 : ℝ → ℝ) ⊆ _; simp only [tsupport_zero, Set.empty_subset])
    0 0 0 0 0 (1/2) (by norm_num) (by norm_num)
  obtain ⟨C,hC,hc⟩ := hb B le_rfl 1 (by norm_num) 1 (by omega) 0
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hs : 1 / Real.sqrt (B : ℝ) ≤ 1 := by
    apply (div_le_one (Real.sqrt_pos.2 (by positivity))).2
    exact (Real.one_le_sqrt).2 hBreal
  have hh := (hc 0 1 (by norm_num) (by norm_num) (by simpa [ringScale] using hs) 0).2.2
    0 (by omega) 0 (by norm_num)
  norm_num [rejected, realize, ringScale, delta] at hh
  exact (not_lt_of_ge (norm_nonneg _)) (lt_of_le_of_lt hh (by norm_num))
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_center_mixed_scales)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_center_mixed_scales, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_center_mixed_scales) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditReferenceCenterMixedScales.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditReferenceCenterMixedScales.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 20
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditReferenceCenterMixedScales

namespace AuditActiveRing
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {xstar x : ℝ} {b j : ℕ}
    (hxstar : 0 < xstar) (hx : 0 < x) (hb : 1 < b)
    (hw : scaleWeight xstar b j x ≠ 0),
    ringScale xstar b j / Real.sqrt b ≤ (R.readout () () x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hden : scaleDenominator 0 = scaleBump 0 := by
    unfold scaleDenominator
    have ht : (∑' i : ℕ, scaleBump (0 - (i : ℝ))) = scaleBump (0 - (0 : ℕ)) :=
      tsum_eq_single 0 (fun (i : ℕ) (hi : i ≠ 0) => show scaleBump (0 - (i : ℝ)) = 0 from by
      apply expNegInvGlue.zero_of_nonpos
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hi)
      nlinarith)
    simpa using ht
  have hpos : 0 < scaleBump 0 := expNegInvGlue.pos_of_pos (by norm_num)
  have hw : scaleWeight 1 4 0 1 ≠ 0 := by
    simp [scaleWeight, scaleCoordinate, hden, ne_of_gt hpos]
  have hh := @h 1 1 4 0 (by norm_num) (by norm_num) (by omega) hw
  norm_num [rejected, realize, ringScale] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.active_ring)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.active_ring, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.active_ring) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditActiveRing.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditActiveRing.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditActiveRing

namespace AuditCoefficientSmooth
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (η a d : ℝ) (r k D t : ℕ)
    {x : ℝ} (hx : 0 < x),
    ContDiffAt ℝ ∞
      (fun y => bernsteinCoefficient D t
        (center τ b r (fun q => (reference φ η a d y q : ℂ)) k)) (R.readout () () x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 1 1 (by omega) (by omega) (fun z : ℝ => z) contDiff_id
    1 1 0 0 0 0 0 1 (by norm_num)
  norm_num [rejected, realize, center, holderOperator, lorentzJet, tau,
    bernsteinCoefficient, bernsteinPolynomial, reference, Finset.sum_range_succ] at hh
  have hr := (Complex.reCLM.contDiff.contDiffAt.comp 0 hh).sub
    (contDiffAt_const (c := (1/2 : ℝ)))
  have hd : DifferentiableAt ℝ (fun y : ℝ => y⁻¹) 0 := by
    simpa using hr.differentiableAt (by simp)
  exact (differentiableAt_inv_iff.mp hd) rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.coefficient_smooth)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.coefficient_smooth, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.coefficient_smooth) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditCoefficientSmooth.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditCoefficientSmooth.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditCoefficientSmooth

namespace AuditReferencePublicArrayRegular
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ),
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar : ℝ, 0 < xstar → xstar ≤ 1 → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ W : ℝ, 0 ≤ W → W*xstar^β ≤ 15/16 →
      let lower := publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β
      let upper := publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β
      (∀ k : ℕ, ∀ x : ℝ, 0 < x → x ≤ xstar →
        (∀ t ≤ N*b^k+r, ContDiffAt ℝ ∞ (lower k t) x ∧ ContDiffAt ℝ ∞ (upper k t) x ∧
          (1/32 : ℝ) ≤ lower k t x ∧ lower k t x ≤ upper k t x ∧ upper k t x ≤ 31/32 ∧
          |lower k t x-1/2| ≤ W*x^β/2 ∧ |upper k t x-1/2| ≤ (R.readout () () W)*x^β/2) ∧
        (∀ t ≤ N*b^(k+1)+r,
          _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun i => lower k i x) ≤ lower (k+1) t x ∧
          upper (k+1) t x ≤ _root_.D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun i => upper k i x))) ∧
      (0 < β → ∀ k t : ℕ, t ≤ N*b^k+r →
        ContinuousOn (lower k t) (Set.Icc 0 xstar) ∧
        ContinuousOn (upper k t) (Set.Icc 0 xstar)) ∧
      (∀ x : ℝ, 0 < x → x ≤ xstar → ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ k : ℕ, K ≤ k → ∀ t ≤ N*b^k+r,
          (upper k t x-lower k t x ≤ C*((N*b^k : ℕ) : ℝ)^(-ρ/2))) ∧
      (∀ x : ℝ, 0 < x → x ≤ xstar → ∀ ε : ℝ, 0 < ε →
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ t ≤ N*b^k+r, upper k t x-lower k t x < ε)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨B,hB,hb⟩ := @h (fun _ => 0) contDiff_const HasCompactSupport.zero 1 0 (by norm_num)
    (by norm_num) (by change tsupport (0 : ℝ → ℝ) ⊆ _; simp only [tsupport_zero, Set.empty_subset]) (by intro t; norm_num) 0 0 2 (5/2) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨D,hD,N,hN,hc⟩ := hb B le_rfl 1 (by norm_num) (by norm_num)
  have hh := ((hc 0 (by norm_num) (by norm_num)).1 0 1 (by norm_num) (by norm_num)).1 0 (by omega)
  have bad := hh.2.2.2.2.2.2
  norm_num [rejected, realize] at bad
  linarith [abs_nonneg (publicUpper (cutoff (fun _ => 0) 0) (2/(5*(1:ℝ)^0))
    0 0 2 (5/2) 1 B N D 1 0 0 0 0 1 - 1/2)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_public_array_regular)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_public_array_regular, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.reference_public_array_regular) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditReferencePublicArrayRegular.unit
  realizationName := `Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport.AuditReferencePublicArrayRegular.family
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
    owner := `D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 26
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end AuditReferencePublicArrayRegular

end Reg.D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
