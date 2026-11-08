import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentLiteralV
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
namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentLiteralV

namespace LiteralEnergy
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => Bool)
def actual : Realization signature := realize signature (fun _ _ z => @decide (0 < z) (Classical.propDecidable _)) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (hq : 1 ≤ q) (D : ℝ) (hD : Real.log 2 + 1 / 16 ≤ D),
    ∃ (x : Fin q × Fin 3 × Bool → ℝ) (a : Fin q × Fin 3 × Bool → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) (1 / 16) ∪ Icc (Real.log 2) (Real.log 2 + 1 / 16)) ∧
      (∀ i, x i ∈ Icc (0 : ℝ) D) ∧
      (∀ m : ℕ, m ≤ q → ∑ i, a i * (x i : ℂ) ^ m = 0) ∧
      (∑ i, a i * (Real.exp (x i / 2) : ℂ) = 0) ∧
      (∑ i, a i * (x i : ℂ) ^ (q + 1)) ≠ 0 ∧
      (∑ i, a i * (x i : ℂ) * (Real.exp (x i / 2) : ℂ)) ≠ 0 ∧
      R.readout () () (energy x a) = true ∧
        V D x a / energy x a ≤ -1 / (65536 * (q : ℝ) ^ 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, a, _, _, _, _, _, _, hp, _⟩ :=
    h 1 (by norm_num) (Real.log 2 + 1 / 16) le_rfl
  change false = true at hp
  cases hp
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @literal_V_energy_moment_obstruction) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
    using @literal_V_energy_moment_obstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@literal_V_energy_moment_obstruction) (Realization signature) (Type) Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate.literal_V_energy_moment_obstruction.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentLiteralV.LiteralEnergy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => @decide (0 < z) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentLiteralV
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end LiteralEnergy


end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentLiteralV
