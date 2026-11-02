/- Exact-telescope Reg source attempts for owner-local realizations consumed
by the full actual-K endpoint. No standalone supplier admission, validation,
sourceSelection path, or compilation is claimed. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
import Reg.Support.SingleDependentReadout
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations

private def rampValue {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (max (t - x i) 0 : ℝ)

private def halfResolvent {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (((1 - Real.exp (-(1 / 2 : ℝ) * max (t - x i) 0)) /
    (1 / 2 : ℝ) : ℝ) : ℂ)

namespace CausalDeficit
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0),
    (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) -
    (∑ i, ∑ j, star (a i) * a j *
      (Real.exp (-|x i - x j| / 2) : ℂ)).re = R.readout () ()
      ((1 / 4) * ((∫ t in Icc (0 : ℝ) D, ‖halfResolvent x a t‖ ^ 2) +
        ‖halfResolvent x a D‖ ^ 2))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  norm_num [rejected, realize, halfResolvent, rampValue, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.causal_prefix_deficit.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.causal_prefix_deficit.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.causal_prefix_deficit.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.causal_prefix_deficit.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.CausalDeficit.family
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
end CausalDeficit

namespace NonnegativeDeficit
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0),
    0 ≤ R.readout () () ((∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) -
    (∑ i, ∑ j, star (a i) * a j *
      (Real.exp (-|x i - x j| / 2) : ℂ)).re)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  norm_num [rejected, realize, halfResolvent, rampValue, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_deficit_nonneg.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_deficit_nonneg.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_deficit_nonneg.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_deficit_nonneg.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.NonnegativeDeficit.family
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
end NonnegativeDeficit

namespace PrimitiveGap
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    R.readout () () (∫ t in Icc (0 : ℝ) D, ‖rampValue x a t‖ ^ 2) ≤
      D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down)
    (by intro r hr; simp)
  norm_num [rejected, realize, halfResolvent, rampValue, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_gap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_gap.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_gap.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_gap.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.PrimitiveGap.family
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
end PrimitiveGap

namespace GrowingPrimitive
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0)
    (hfirst : ∑ i, a i * (x i : ℂ) = 0),
    let G : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t, «prefix» x a u
    let h : ℝ → ℂ := fun t => ∫ u in (0 : ℝ)..t,
      (Real.exp ((t - u) / 2) : ℂ) * G u
    G 0 = 0 ∧ G D = 0 ∧
      R.readout () () (∑ i, ∑ j, star (a i) * a j *
      (Real.exp (|x i - x j| / 2) : ℂ)) =
        -(∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) + (1 / 4) * (∫ t in Icc (0 : ℝ) D, ‖G t‖ ^ 2) +
          (1 / 16) * (2 * ∫ t in Icc (0 : ℝ) D, (star (G t) * h t).re)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp) (by simp)
  norm_num [rejected, realize, halfResolvent, rampValue, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.growing_primitive_identity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.growing_primitive_identity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.growing_primitive_identity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.growing_primitive_identity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.GrowingPrimitive.family
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
end GrowingPrimitive

namespace PrimitiveRealization
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, 0 ≤ x i) (t : ℝ) (ht : 0 ≤ t),
    (∫ u in (0 : ℝ)..t, «prefix» x a u) = R.readout () () (rampValue x a t)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) 0 le_rfl
  norm_num [rejected, realize, halfResolvent, rampValue, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_realization.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_realization.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_realization.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.actual_prefix_primitive_realization.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.PrimitiveRealization.family
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
end PrimitiveRealization

namespace GrowingCorrelation
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0),
    R.readout () () (∑ i, ∑ j, star (a i) * a j *
      (Real.exp (|x i - x j| / 2) : ℂ)) = -(∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) -
      (1 / 2) * ∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) *
        (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  norm_num [rejected, realize, halfResolvent, rampValue, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.growing_exponential_correlation_identity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.GrowingCorrelation.family
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
end GrowingCorrelation

/- Coverage of the retained public supplier only. Its historic admission
is not reopened and this creates no separate content request. -/
namespace RetainedMomentSupplier
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (hlam : 0 < lam)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    2 * lam * (1 - lam ^ 2 * D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) *
      (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) ≤
        R.readout () () (∑ i, ∑ j, star (a i) * a j *
          (Real.exp (-lam * |x i - x j|) : ℂ))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 1 (by norm_num) 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down)
    (by intro r hr; simp)
  norm_num [rejected, realize, halfResolvent, rampValue, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℂ).re ≠ (1 : ℂ).re; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.moment_exponential_prefix_coercivity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.moment_exponential_prefix_coercivity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.moment_exponential_prefix_coercivity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.moment_exponential_prefix_coercivity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.RetainedMomentSupplier.family
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
end RetainedMomentSupplier

/- Retained arithmetic suppliers: coverage only, not a new admission. -/
namespace RetainedWeightedTail
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {c D X x : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hX : 2 ≤ X) (hx : X ≤ x)
    (hpsi : ∀ u ≥ X, |Chebyshev.psi u - u| ≤
      D * (u * _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate (2 * c) u)),
    |∫ u in Ioi x, (Chebyshev.psi u - u) / u ^ 2| ≤ R.readout () ()
      (D * (∫ u in Ioi 1, _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.weight c u) *
        _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate c x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c₀, hc₀, hO⟩ := MediumPNT
  obtain ⟨D, hD, hbound⟩ := isBigO_iff'.mp hO
  obtain ⟨A, hA⟩ := eventually_atTop.mp hbound
  let X : ℝ := max A 2
  let c : ℝ := c₀ / 2
  have hX : (2 : ℝ) ≤ X := le_max_right _ _
  have hc : 0 < c := by dsimp [c]; positivity
  have hdouble : 2 * c = c₀ := by dsimp [c]; ring
  have hpsi (u : ℝ) (hu : X ≤ u) : |Chebyshev.psi u - u| ≤
      D * (u * _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate (2 * c) u) := by
    have hu0 : 0 < u := by linarith
    have huA : A ≤ u := (le_max_left A 2).trans hu
    simpa only [_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate, hdouble,
      Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul, abs_of_pos hu0,
      abs_of_pos (Real.exp_pos _)] using hA u huA
  have h0 := h hc hD.le hX (show X ≤ X from le_rfl) hpsi
  change |∫ u in Ioi X, (Chebyshev.psi u - u) / u ^ 2| ≤ (-1 : ℝ) at h0
  linarith only [h0, abs_nonneg (∫ u in Ioi X, (Chebyshev.psi u - u) / u ^ 2)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.RetainedWeightedTail.family
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
end RetainedWeightedTail

namespace RetainedWeightedEndpoint
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∃ c > 0, ∃ C > 0, ∃ X ≥ (2 : ℝ), ∀ x ≥ X,
    |_root_.Mertens.E₁Λ x + Real.eulerMascheroniConstant| ≤
      R.readout () () (C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc, C, hC, X, hX, hb⟩ := h
  have h0 := hb X le_rfl
  change |_root_.Mertens.E₁Λ X + Real.eulerMascheroniConstant| ≤ (-1 : ℝ) at h0
  linarith only [h0, abs_nonneg (_root_.Mertens.E₁Λ X + Real.eulerMascheroniConstant)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations.RetainedWeightedEndpoint.family
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
end RetainedWeightedEndpoint

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentOwnerRealizations
