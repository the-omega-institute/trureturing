import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.MobiusDyadicEnergy
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import Reg.Support.SingleDependentReadout

/-! The accumulated shell energy is the readout at every finite cutoff. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.MobiusDyadicEnergy
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (exists_nontrivial_zero_re_ge_half)

namespace Reg.D5.S3.Weil.Mertens.MobiusDyadicEnergy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ N => ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {rho : ℂ}, (1 / 2 : ℝ) ≤ rho.re → rho.re < 1 → riemannZeta rho = 0 →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * K rho.re ((N : ℝ) * Real.log 2) ≤ R.readout () () N

private theorem right_half_zero :
    ∃ rho : ℂ, (1 / 2 : ℝ) ≤ rho.re ∧ rho.re < 1 ∧ riemannZeta rho = 0 := by
  obtain ⟨rho, hr, hh⟩ := exists_nontrivial_zero_re_ge_half
  exact ⟨rho, hh, hr.2.2, hr.1⟩

private theorem positive_scale (beta : ℝ) {N : ℕ} (hN : 0 < N) :
    0 < K beta ((N : ℝ) * Real.log 2) := by
  have hu : 0 < (N : ℝ) * Real.log 2 :=
    mul_pos (Nat.cast_pos.mpr hN) (Real.log_pos (by norm_num))
  exact intervalIntegral.integral_pos hu
    (by fun_prop) (fun _ _ => (Real.exp_pos _).le)
    ⟨0, ⟨le_rfl, hu.le⟩, Real.exp_pos _⟩

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨rho, hh, hl, hz⟩ := right_half_zero
  obtain ⟨c, hc, N₀, hbound⟩ := h hh hl hz
  have hle := hbound (N₀ + 1) (Nat.le_succ N₀)
  change c * K rho.re (((N₀ + 1 : ℕ) : ℝ) * Real.log 2) ≤ 0 at hle
  exact (not_le_of_gt (mul_pos hc (positive_scale _ (Nat.succ_pos N₀)))) hle

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  obtain ⟨rho, hh, hl, hz⟩ := right_half_zero
  obtain ⟨c, hc, N₀, hbound⟩ := signed_dyadic_eventual_prefix_lower_bound hh hl hz
  have hpos := (mul_pos hc (positive_scale rho.re (Nat.succ_pos N₀))).trans_le
    (hbound (N₀ + 1) (Nat.le_succ N₀))
  refine ⟨(), 0, N₀ + 1, ?_⟩
  change (∑ k ∈ Finset.range 0, mobiusDyadicShellEnergy k) ≠
    ∑ k ∈ Finset.range (N₀ + 1), mobiusDyadicShellEnergy k
  rw [Finset.sum_range_zero]
  exact hpos.ne

def evidence : Registration arena (type_of% @signed_dyadic_eventual_prefix_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_dyadic_eventual_prefix_lower_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signed_dyadic_eventual_prefix_lower_bound) (Realization signature) (ℕ → ℝ) Unit where
  unitName :=
    `D5.S3.Weil.Mertens.MobiusDyadicEnergy.signed_dyadic_eventual_prefix_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.MobiusDyadicEnergy.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.MobiusDyadicEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "arg", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.MobiusDyadicEnergy
