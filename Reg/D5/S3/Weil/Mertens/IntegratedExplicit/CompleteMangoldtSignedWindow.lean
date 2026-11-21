import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow

/-! A perturbation of the completed transform changes the signed moment bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set LeanInformationAudit
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne (completed)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne (signature actual)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow

private def tailAtTwo : ℝ :=
  ∫ u in Ioi (0 : ℝ) \ Icc 1 1, |U (Real.exp u)| * Real.exp (-2 * u)

def constantTransform : Realization signature :=
  realize signature (fun _ _ _ => (|tailAtTwo| + 1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V :=
    ∀ (k : ℕ) {p : ℂ}, 1 < p.re →
      ∀ {a b α e : ℝ}, 0 < a → a ≤ b → α < p.re → (e = 1 ∨ e = -1) →
      let D := fun s : ℂ => ((-1 : ℂ) ^ k / k.factorial) * iteratedDeriv k (V.readout () ()) s
      let g := fun u : ℝ => U (Real.exp u)
      ‖D p‖ + e * (D (p.re : ℂ)).re ≤
        2 * (p.re - α)⁻¹ ^ k * (∫ u in a..b, max (e * g u) 0 * Real.exp (-α * u)) +
        2 * ∫ u in Ioi (0 : ℝ) \ Icc a b,
          |g u| * (u ^ k * Real.exp (-p.re * u) / k.factorial)

private theorem constantTransform_fails : ¬ arena.Law constantTransform := by
  intro h
  have htest := h 0 (p := 2) (by norm_num) (a := 1) (b := 1) (α := 0) (e := 1)
    (by norm_num) le_rfl (by norm_num) (Or.inl rfl)
  have hnonneg : 0 ≤ |tailAtTwo| + (1 : ℝ) := by positivity
  have hread (z : ℂ) : constantTransform.readout () () z = ((|tailAtTwo| + 1 : ℝ) : ℂ) := rfl
  simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    hread, Complex.norm_of_nonneg hnonneg, Complex.ofReal_re, intervalIntegral.integral_same,
    mul_zero, zero_add] at htest
  change (|tailAtTwo| + 1) + (|tailAtTwo| + 1) ≤ 2 * tailAtTwo at htest
  linarith [le_abs_self tailAtTwo]

def evidence : Registration arena (type_of% @signed_window_moment_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨signed_window_moment_bound, constantTransform, constantTransform_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual constantTransform constantTransform_fails
  dependence :=
    _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtAtOne.evidence.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signed_window_moment_bound) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow.signed_window_moment_bound
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => completed) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "value", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtSignedWindow
