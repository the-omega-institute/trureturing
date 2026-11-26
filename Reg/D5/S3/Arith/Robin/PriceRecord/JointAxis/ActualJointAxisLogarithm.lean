import D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Varying the literal budget readout tests its role in joint nonvanishing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm

open LeanInformationAudit Real Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open _root_.D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover (jointSquare)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport
  (boxSizes coordinates transportConstant)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock (reference reference_pos)
open _root_.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm (omegaThree)
open _root_.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm

namespace LiteralBudget

abbrev readoutSignature := signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℤ, Σ _ : ℝ, Σ _ : ℤ, Fin 3 → ℤ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ p w => jointSquare (boxSizes p.1 p.2.1 p.2.2.2.1) p.2.2.2.2.1 p.2.2.2.2.2
      (coordinates (exp (reference p.2.2.1))) w) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature
    (fun _ _ _ => 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {β κζ : ℝ}, (37 / 50 ≤ β ∧ β < 3 / 4) → 0 < κζ →
    ∀ᶠ e : ℤ in atTop,
      ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ},
        let L := reference e
        let Y := exp L
        let K := transportConstant κζ
        |L - Lbar| ≤ 1 → 1 ≤ h → (h : ℝ) ≤ exp (L / 50) →
        R.readout () ⟨β, κζ, e, Lbar, h, p⟩ w ≤ (43 : ℝ) / 9 →
        let Ω := omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ)
        Ω ≠ 0 ∧ |Ω| ≤ (50 * K + 1) * exp (-(L / 15)) / L ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro ha
  obtain ⟨e, he⟩ := (ha (β := 37 / 50) (κζ := 1) (by norm_num) one_pos).exists
  have hc : |reference e - reference e| ≤ 1 := by simp
  have hden : (1 : ℝ) ≤ exp (reference e / 50) :=
    one_le_exp_iff.mpr (div_nonneg (reference_pos e).le (by norm_num))
  have hb := (he (Lbar := reference e) (w := 0) (h := 1) (p := fun _ => 0)
    hc (by decide) (by simpa using hden) (by norm_num [rejected, realize])).1
  exact hb (by simp [omegaThree])

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨0, 1, 0, 0, 1, fun _ => 0⟩, 0, 1, ?_⟩
  change jointSquare (boxSizes 0 1 0) 1 (fun _ => 0) (coordinates (exp (reference 0))) 0 ≠
    jointSquare (boxSizes 0 1 0) 1 (fun _ => 0) (coordinates (exp (reference 0))) 1
  intro he
  simp only [jointSquare, Int.cast_one, mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow,
    add_zero] at he
  linarith only [he]

def family : Registration arena (type_of% @eventually_clock_joint_logarithm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventually_clock_joint_logarithm, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventually_clock_joint_logarithm) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm.LiteralBudget.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm.LiteralBudget.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize readoutSignature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm
    definition := none
    coordinates := #[0, 1, 4, 5, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "domain", "fn",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LiteralBudget

end Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualJointAxisLogarithm
