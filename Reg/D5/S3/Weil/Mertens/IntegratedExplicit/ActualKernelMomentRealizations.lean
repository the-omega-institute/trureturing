/- Reg source attempts for consumed concrete realizations in the SAME full
actual-K payload. Not separate content requests. No sourceSelection path is
invented and no validation or compilation is claimed. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
import Reg.Support.SingleDependentReadout
noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentRealizations

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
  norm_num [rejected, realize, energy, quadratic, W, S, correlation, V, Z, «prefix»] at h0
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
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentRealizations.Mixture.family
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


namespace Resolvent
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    0 ≤ R.readout () () (W D x a) ∧ (∀ t : ℝ, |S D x a t| ≤ W D x a) ∧
      W D x a ≤ D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * energy x a / 4 ∧
        |Z D x a| ≤ 4 * M D * W D x a
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by intro r hr; simp)
  norm_num [rejected, realize, energy, quadratic, W, S, correlation, V, Z, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @actual_resolvent_control.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_resolvent_control.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_resolvent_control.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_resolvent_control.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentRealizations.Resolvent.family
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
end Resolvent


namespace Cutoff
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => |z|) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (p : PNTConstants)
    (D : ℝ) (hD : 0 < D) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0),
    R.readout () () (V D x a) ≤ (8 + 4 * p.C + 2 * B p) * M D * W D x a
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance pnt 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  norm_num [rejected, realize, energy, quadratic, W, S, correlation, V, Z, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change |(0 : ℝ)| ≠ |(1 : ℝ)|; norm_num⟩
def family : Registration arena.{u} (type_of% @actual_cutoff_resolvent_payment.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_cutoff_resolvent_payment.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_cutoff_resolvent_payment.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_cutoff_resolvent_payment.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentRealizations.Cutoff.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => |z|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cutoff


namespace Continuum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    -((M D + D + 3) / 4) * (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a ≤
      R.readout () () (continuum D x a)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by intro r hr; simp)
  norm_num [rejected, realize, energy, quadratic, W, S, correlation, V, Z, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @actual_continuum_moment_payment.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_continuum_moment_payment.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_continuum_moment_payment.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_continuum_moment_payment.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentRealizations.Continuum.family
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
end Continuum


namespace FullR
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0),
    R.readout () () (-(1 / 2) * (∫ t in Icc (0 : ℝ) D, fullR t * correlation x a t)) =
      d0 * W D x a + V D x a
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by simp)
  norm_num [rejected, realize, energy, quadratic, W, S, correlation, V, Z, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @actual_fullR_resolvent_identity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_fullR_resolvent_identity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_fullR_resolvent_identity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_fullR_resolvent_identity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentRealizations.FullR.family
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
end FullR

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentRealizations
