import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture
import Reg.Support.SingleDependentReadout
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture

namespace Mixture
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (hr : 8 ≤ (q : ℝ) / D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    (Real.log ((q : ℝ) / D) - 1) * energy x a ≤ R.readout () () (quadratic x a P)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 8 (by norm_num) (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by intro r hr; simp)
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, energy, quadratic, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩
def family : Registration arena.{u} (type_of% @complete_positive_mixture_logarithmic.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complete_positive_mixture_logarithmic.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_positive_mixture_logarithmic.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.complete_positive_mixture_logarithmic.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture.Mixture.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Mixture



/- The complete original multiplier telescope is retained. Only the logarithm
   in the lower bound is varied; the upper bound and full series stay fixed. -/
namespace Multiplier
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ t => Real.log t) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ ξ : ℝ,
    Summable (fun n : ℕ =>
      (2 * rate n * trivialCoeff n) * ξ ^ 2 / (rate n ^ 2 + ξ ^ 2)) ∧
    0 ≤ pMultiplier ξ ∧ pMultiplier 0 = 0 ∧
    R.readout () () (2 + |ξ|) - Real.log 13 / 2 ≤ pMultiplier ξ ∧
    pMultiplier ξ ≤ Real.log (2 + |ξ|) + 1 - Real.log 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 0).2.2.2.1
  have hl : Real.log 13 ≤ 12 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13)]
  change (100 : ℝ) - Real.log 13 / 2 ≤ pMultiplier 0 at hb
  rw [(pMultiplier_logarithmic_bounds 0).2.2.1] at hb
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact ne_of_lt (Real.log_pos (by norm_num))
def family : Registration arena (type_of% @pMultiplier_logarithmic_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pMultiplier_logarithmic_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pMultiplier_logarithmic_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.pMultiplier_logarithmic_bounds.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture.Multiplier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => Real.log t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Multiplier

/- The actual complex real-part readout is selected in the full spectral
   statement; the literal actual density and integrability clause are fixed. -/
namespace Spectral
abbrev signature : Signature := Mixture.signature
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0),
    Integrable pMultiplier (OriginalActualFourier.rho («prefix» x a)) ∧
      R.readout () () (quadratic x a P) =
        ∫ ξ, pMultiplier ξ ∂OriginalActualFourier.rho («prefix» x a)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 0 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  have he := h0.2
  norm_num [rejected, realize, OriginalActualFourier.rho,
    OriginalActualFourier.density, OriginalActualFourier.Ahat, «prefix»] at he
def family : Registration arena.{u}
    (type_of% @complete_positive_mixture_spectral_identity.{u}) where
  actual := Mixture.actual
  bridge := Iff.rfl
  variation := ⟨@complete_positive_mixture_spectral_identity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law Mixture.actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature Mixture.actual
    exact Mixture.dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_positive_mixture_spectral_identity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.complete_positive_mixture_spectral_identity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture.Spectral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Spectral

namespace GammaHead
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 < D)
    (q : ℕ) (hq : 1 ≤ q) (M m : ℕ) (hmpos : 1 ≤ m)
    (ham : D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) ≤ 1 / (m : ℝ))
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    (∑ n ∈ Finset.range M,
      trivialCoeff n *
        (2 * rate n / (1 + rate n ^ 2 / (m : ℝ)))) * energy x a ≤
      R.readout () () (quadratic x a P).re
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 1 (by norm_num)
    20 1 (by norm_num) (by norm_num) (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by intro r hr; simp)
  dsimp only [rejected, realize] at h0
  norm_num [energy, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.complete_positive_mixture_head_gamma.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.complete_positive_mixture_head_gamma.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.complete_positive_mixture_head_gamma.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.complete_positive_mixture_head_gamma.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture.GammaHead.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end GammaHead

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentMixture
