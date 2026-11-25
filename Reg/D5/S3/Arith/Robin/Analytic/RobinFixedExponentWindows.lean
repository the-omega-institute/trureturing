import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows
import Reg.D5.S3.Weil.Mertens.WeightedTailInverse

/-! Register the ordinary tail shared by the window hypothesis and signed mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set MeasureTheory Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.WeightedTailTransport (tail weightedTail)
open _root_.D5.S3.Weil.Mertens.WeightedTailInverse (a)
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows
open _root_.Reg.D5.S3.Weil.Mertens.WeightedTailInverse (signature actual inverseEvidence)

namespace Reg.D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows

private def rejected : Realization signature :=
  realize signature (fun _ _ _ x => x + |a x * weightedTail psiErrorKernel x|)
    (fun impossible => nomatch impossible)

def arena : Arena where
  signature := signature
  Law V := ∀ {κ b : ℝ}, 0 < κ → κ < 1 / 2 → 1 < b →
    let observe := V.readout () ()
    let q := observe psiErrorKernel
    (∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ᶠ Y : ℝ in atTop,
      ∀ x ∈ Icc Y (Y ^ b), -x * q x ≤ C₀ * x ^ (1 / 2 + κ)) →
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ x : ℝ, exp 1 ≤ x →
        |q x - a x * weightedTail psiErrorKernel x| ≤ K * x ^ (κ - 1 / 2) / log x) ∧
      (∀ A B e : ℝ, exp 1 ≤ A → A ≤ B → (e = 1 ∨ e = -1) →
        |(∫ t in A..B, (a t / sqrt t) * max (e * (-weightedTail psiErrorKernel t)) 0) -
          (∫ t in A..B, max (e * (-q t)) 0 / sqrt t)| ≤
          (K / (κ * log A)) * (B ^ κ - A ^ κ))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hwindow : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ᶠ Y : ℝ in atTop,
      ∀ x ∈ Icc Y (Y ^ (2 : ℝ)),
        -x * (x + |a x * weightedTail psiErrorKernel x|) ≤ C₀ * x ^ (1 / 2 + 1 / 4 : ℝ) := by
    refine ⟨0, le_rfl, ((eventually_ge_atTop (1 : ℝ)).mono ?_).frequently⟩
    intro Y hY x hx
    rw [zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (zero_le_one.trans (hY.trans hx.1)))
      (add_nonneg (zero_le_one.trans (hY.trans hx.1)) (abs_nonneg _))
  obtain ⟨K, hK, hdef, _⟩ := h (κ := 1 / 4) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) hwindow
  let x : ℝ := max (exp 1) (K + 1)
  have hx := le_max_left (exp 1) (K + 1)
  have hx1 : 1 ≤ x := (one_le_exp_iff.mpr zero_le_one).trans hx
  have hlog : 1 ≤ log x := by
    simpa only [log_exp] using log_le_log (exp_pos 1) hx
  have hpow : x ^ ((1 / 4 : ℝ) - 1 / 2) ≤ 1 := by
    simpa only [rpow_zero] using
      (rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 4 : ℝ) - 1 / 2 ≤ 0))
  have hupper := hdef x hx
  change |x + |a x * weightedTail psiErrorKernel x| - a x * weightedTail psiErrorKernel x| ≤ _ at hupper
  have hleft : x ≤ |x + |a x * weightedTail psiErrorKernel x| -
      a x * weightedTail psiErrorKernel x| := by
    exact (by linarith only [le_abs_self (a x * weightedTail psiErrorKernel x)] :
      x ≤ x + |a x * weightedTail psiErrorKernel x| - a x * weightedTail psiErrorKernel x).trans
      (le_abs_self _)
  have hright : K * x ^ ((1 / 4 : ℝ) - 1 / 2) / log x ≤ K := by
    exact (div_le_self (mul_nonneg hK (rpow_nonneg (zero_le_one.trans hx1) _))
      hlog).trans (mul_le_of_le_one_right hK hpow)
  linarith only [hleft.trans (hupper.trans hright), le_max_right (exp 1) (K + 1)]

def evidence : Registration arena (type_of% @signed_mass_comparison_of_frequently_window_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_mass_comparison_of_frequently_window_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := inverseEvidence.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signed_mass_comparison_of_frequently_window_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows.signed_mass_comparison_of_frequently_window_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => tail k) (fun impossible => nomatch impossible))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Reg.D5.S3.Arith.Robin.Analytic.RobinFixedExponentWindows
end
