import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
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
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

namespace OriginalTarget

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Literal original target arena, not a positive law or a registration. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ), 0 < D →
    ∀ (x : I → ℝ) (a : I → ℂ), (∀ i, x i ∈ Icc (0 : ℝ) D) →
      (∀ r : ℕ, r ≤ order pnt D → ∑ i, a i * (x i : ℂ) ^ r = 0) →
    energy x a ≤ R.readout () ()
      (quadratic x a _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.K)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down)
    (by intro r hr; simp)
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, energy, «prefix»] at h0


private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena.{u} (type_of% @actual_kernel_explicit_leading_one.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_kernel_explicit_leading_one.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_kernel_explicit_leading_one.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_kernel_explicit_leading_one.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.OriginalTarget.family
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

end OriginalTarget


namespace SignedExpression
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 < D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ order pnt D → ∑ i, a i * (x i : ℂ) ^ r = 0),
    (Real.log (2 * Real.pi) - 1 - Real.eulerMascheroniConstant) *
      (energy x a - W D x a) - (quadratic x a P).re + energy x a ≤
        R.readout () () (signedJExpression D x a)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 1 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down)
    (by intro r hr; simp)
  norm_num [rejected, realize, energy, quadratic, W, S, correlation,
    signedJExpression, primeQuadratic, continuum, V, Z, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena.{u} (type_of% @actual_signed_expression_compensation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_signed_expression_compensation.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_signed_expression_compensation.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_signed_expression_compensation.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.SignedExpression.family
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
end SignedExpression





namespace ScalarBounds

abbrev claim : Prop := type_of% @ActualKScalarSource.q_scalar_bounds

abbrev signature : Signature :=
  { Params := Unit
    State := fun _ => Bool
    Role := Unit
    finiteRole := inferInstance
    nonemptyRole := inferInstance
    Output := fun _ _ => Prop × Bool
    Anchor := Empty
    finiteAnchor := inferInstance }

def actual : Realization signature :=
  realize signature (fun _ _ state => (if state then True else claim, state))
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ state => (False, state)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := (R.readout () () false).1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  intro h
  have hs := congrArg Prod.snd h
  cases hs

def family : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ActualKScalarSource.q_scalar_bounds, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ActualKScalarSource.q_scalar_bounds) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.ActualKScalarSource.q_scalar_bounds.audit
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.ScalarBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end ScalarBounds

namespace Q6SmallWindow

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD0 : 0 ≤ D)
    (hD3 : D ≤ Real.log 3) (q : ℕ) (hq : 6 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    (36 / 575 : ℝ) * energy x a ≤ R.readout () ()
      (quadratic x a _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.K)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 0 (by norm_num)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); linarith)
    6 (by norm_num) (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by intro r hr; simp)
  dsimp only [rejected, realize] at h0
  norm_num [energy, quadratic, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num
def family : Registration arena.{u} (type_of% @actual_kernel_q6_small_window.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_kernel_q6_small_window.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_kernel_q6_small_window.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_kernel_q6_small_window.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.Q6SmallWindow.family
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

end Q6SmallWindow

namespace Q22SmallWindow

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD0 : 0 ≤ D)
    (hD3 : D ≤ Real.log 3) (q : ℕ) (hq : 22 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0),
    (2017 / 2000 : ℝ) * energy x a ≤ R.readout () ()
      (quadratic x a _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.K) ∧
    energy x a ≤ R.readout () ()
      (quadratic x a _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.K)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 0 (by norm_num)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); linarith)
    22 (by norm_num) (fun _ => 0) (fun _ => 0)
    (by intro i; exact Empty.elim i.down) (by intro r hr; simp)
  dsimp only [rejected, realize] at h0
  norm_num [energy, quadratic, «prefix»] at h0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num
def family : Registration arena.{u} (type_of% @actual_kernel_q22_small_window.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_kernel_q22_small_window.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_kernel_q22_small_window.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.actual_kernel_q22_small_window.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.Q22SmallWindow.family
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

end Q22SmallWindow

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
