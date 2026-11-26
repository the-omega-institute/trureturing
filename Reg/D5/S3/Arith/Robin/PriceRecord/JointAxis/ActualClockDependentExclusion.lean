import D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The literal budget readout for label bounds and rational independence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion

open LeanInformationAudit Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open _root_.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion
open Filter
open _root_.D5.S3.Arith.DiophantineApproximation.AffineCongruenceIntegerBoxThreeCover (jointSquare)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeFloorBudgetTransport (boxSizes coordinates)
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedBIntegerClock (reference reference_pos)
open _root_.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence (RationalPowerIndependent)

abbrev readoutSignature := signature
  (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℤ, Σ _ : ℝ, Σ _ : ℤ, Fin 3 → ℤ)
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ p w => jointSquare (boxSizes p.1 p.2.1 p.2.2.2.1)
    p.2.2.2.2.1 p.2.2.2.2.2 (coordinates (exp (reference p.2.2.1))) w) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨0, 1, 0, 0, 1, fun _ => 0⟩, 0, 1, ?_⟩
  change jointSquare (boxSizes 0 1 0) 1 (fun _ => 0) (coordinates (exp (reference 0))) 0 ≠
    jointSquare (boxSizes 0 1 0) 1 (fun _ => 0) (coordinates (exp (reference 0))) 1
  intro he
  simp only [jointSquare, Int.cast_one, mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow,
    add_zero] at he
  linarith only [he]

namespace LabelSizes

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {β κζ : ℝ}, (37 / 50 ≤ β ∧ β < 3 / 4) → 0 < κζ →
    ∀ᶠ e : ℤ in atTop,
      ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ},
        let L := reference e
        |L - Lbar| ≤ 1 → 1 ≤ h →
        R.readout () ⟨β, κζ, e, Lbar, h, p⟩ w ≤ (43 : ℝ) / 9 →
        ∃ H P Q : ℕ, (H : ℤ) = h ∧ (P : ℤ) = p 0 ∧ (Q : ℤ) = p 1 ∧
          0 < H ∧ 2 * H ≤ P ∧ H ≤ Q ∧ Q ≤ 3 * H ∧ (P : ℝ) ≤ 3 * L * H

private theorem rejected_law : ¬ arena.Law rejected := by
  intro ha
  obtain ⟨e, he⟩ := (ha (β := 37 / 50) (κζ := 1) (by norm_num) one_pos).exists
  obtain ⟨H, P, _, _, hP, _, hH, hHP, _⟩ :=
    he (Lbar := reference e) (w := 0) (h := 1) (p := fun _ => 0)
      (by simp) (by decide) (by norm_num [rejected, realize])
  omega

def family : Registration arena (type_of% @eventually_clock_label_sizes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventually_clock_label_sizes, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventually_clock_label_sizes) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion.LabelSizes.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion.LabelSizes.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion
    definition := none
    coordinates := #[0, 1, 4, 5, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LabelSizes

namespace Independence

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {β κζ : ℝ}, (37 / 50 ≤ β ∧ β < 3 / 4) → 0 < κζ →
    ∀ᶠ e : ℤ in atTop,
      ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ},
        let L := reference e
        |L - Lbar| ≤ 1 → 1 ≤ h → (h : ℝ) ≤ exp (L / 50) →
        R.readout () ⟨β, κζ, e, Lbar, h, p⟩ w ≤ (43 : ℝ) / 9 →
        RationalPowerIndependent
          (3 * (p 0 : ℚ) / ((p 0 : ℚ) + (p 1 : ℚ)))
          (2 * (p 0 : ℚ) / ((p 0 : ℚ) + (h : ℚ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro ha
  obtain ⟨e, he⟩ := (ha (β := 37 / 50) (κζ := 1) (by norm_num) one_pos).exists
  have hden : (1 : ℝ) ≤ exp (reference e / 50) :=
    one_le_exp_iff.mpr (div_nonneg (reference_pos e).le (by norm_num))
  have hi := he (Lbar := reference e) (w := 0) (h := 1) (p := fun _ => 0)
    (by simp) (by decide) (by simpa using hden) (by norm_num [rejected, realize])
  exact hi ⟨1, 1, by decide, by decide, by norm_num⟩

def family : Registration arena (type_of% @eventually_actual_clock_independent) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@eventually_actual_clock_independent, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eventually_actual_clock_independent) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion.Independence.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion.Independence.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion
    definition := none
    coordinates := #[0, 1, 4, 5, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Independence

end Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.ActualClockDependentExclusion
