import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments
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
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments

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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments.Cutoff.family
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
  dsimp only [rejected, realize] at h0
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
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments.Continuum.family
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



end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentPayments
