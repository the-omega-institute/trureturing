import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
import Reg.Support.SingleDependentReadout
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity

private def halfResolvent {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (((1 - Real.exp (-(1 / 2 : ℝ) * max (t - x i) 0)) / (1 / 2 : ℝ) : ℝ) : ℂ)

private def rampValue {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, a i * (max (t - x i) 0 : ℝ)

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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.CausalDeficit.family
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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.NonnegativeDeficit.family
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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.PrimitiveGap.family
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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.GrowingPrimitive.family
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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.PrimitiveRealization.family
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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.RetainedMomentSupplier.family
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


namespace GammaCoercivity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (lam : ℝ) (hlam : 0 < lam) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (hfirst : ∑ i, a i * (x i : ℂ) = 0),
    2 * lam * (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) ^ 2 ≤ R.readout () ()
      (((∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) + lam ^ 2 *
        (∫ t in Icc (0 : ℝ) D, ‖rampValue x a t‖ ^ 2)) * (∑ i, ∑ j, star (a i) * a j *
          (Real.exp (-lam * |x i - x j|) : ℂ)).re)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    1 (by norm_num) (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by simp) (by simp)
  dsimp only [rejected, realize] at h0
  norm_num [«prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_coercivity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_coercivity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_coercivity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_coercivity.audit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.GammaCoercivity.family
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
end GammaCoercivity

namespace KernelNonnegative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (lam : ℝ) (hlam : 0 < lam) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D),
    0 ≤ R.readout () () (∑ i, ∑ j, star (a i) * a j *
          (Real.exp (-lam * |x i - x j|) : ℂ)).re
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    1 (by norm_num) (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down)
  dsimp only [rejected, realize] at h0
  norm_num [«prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_kernel_nonneg.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_kernel_nonneg.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_kernel_nonneg.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_kernel_nonneg.audit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.KernelNonnegative.family
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
end KernelNonnegative

namespace GammaGapCoercivity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 < D)
    (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (hlam : 0 < lam)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    2 * lam * (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2) ^ 2 ≤ R.readout () ()
      (((1 + lam ^ 2 * (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)))) *
        (∫ t : ℝ, ‖«prefix» x a t‖ ^ 2)) * (∑ i, ∑ j, star (a i) * a j *
          (Real.exp (-lam * |x i - x j|) : ℂ)).re)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num) 1 (by norm_num)
    1 (by norm_num) (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by intro r hr; simp)
  dsimp only [rejected, realize] at h0
  norm_num [«prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.exponential_prefix_gamma_gap_coercivity.audit
  realizationName := `Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity.GammaGapCoercivity.family
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
end GammaGapCoercivity

end Reg.D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
