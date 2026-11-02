import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
import Reg.Support.SingleDependentReadout
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open _root_.D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation

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
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, «prefix»] at h0
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
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.GrowingCorrelation.family
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


namespace Correlation

/- New correlation registration attempt only. Original registrations above
   are retained verbatim. No new sourceSelection path has been verified. -/

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {I : Type u} [Fintype I] (D : ℝ) (hD : 0 ≤ D)
    (N : ℕ) (hN : Real.exp D < N) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0),
    R.readout () () (∑ i, ∑ j, star (a i) * a j *
      ((ActualKernelLocalPositivity.K (x i - x j) -
        Real.exp (-|x i - x j| / 2) * trivialT |x i - x j| : ℝ) : ℂ)) =
    -(Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)) *
      (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) -
    2 * (∑ n ∈ Finset.Icc 2 ⌊Real.exp D⌋₊,
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        (∫ v : ℝ, star («prefix» x a (v + Real.log n)) * «prefix» x a v).re) +
    2 * (∫ s in Icc 0 D, Real.exp (s / 2) *
      (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re) -
    (1 / 2) * (∫ s in Icc 0 D,
      (ActualKernelLocalPositivity.K s - Real.exp (-|s| / 2) * trivialT |s|) *
        (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have h0 := @h (ULift.{u} Empty) inferInstance 0 (by norm_num) 2 (by norm_num)
    (fun _ => 0) (fun _ => 0) (by intro i; exact Empty.elim i.down) (by simp)
  dsimp only [rejected, realize] at h0
  norm_num [rejected, realize, «prefix»] at h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def family : Registration arena.{u} (type_of% @actual_remainder_correlation_identity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_remainder_correlation_identity.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_remainder_correlation_identity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.actual_remainder_correlation_identity.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation.Correlation.family
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

end Correlation

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
