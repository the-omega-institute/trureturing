import D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Observations for the divisor bound and the nonzero dependent form. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence

open LeanInformationAudit Real
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open _root_.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
open _root_.D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm (omegaThree)

private theorem equal_bases_dependent :
    ¬ RationalPowerIndependent (3 * (3 : ℚ) / (3 + 3)) (2 * (3 : ℚ) / (3 + 1)) := by
  intro hind
  exact hind ⟨1, 1, by decide, by decide, by norm_num⟩

namespace NumeratorDivisibility

abbrev readoutSignature := signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ _ p => 2 * p) (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {h p q : ℕ}, 0 < h → 2 * h ≤ p → q ≤ 3 * h →
    let α : ℚ := 3 * (p : ℚ) / ((p : ℚ) + q)
    let β : ℚ := 2 * (p : ℚ) / ((p : ℚ) + h)
    ¬ RationalPowerIndependent α β ↔
      ∃ (A B : ℕ) (t : ℚ), 0 < A ∧ 0 < B ∧ B.Coprime A ∧ 1 < t ∧
        α = t ^ A ∧ β = t ^ B ∧ t.num.toNat ^ B ∣ R.readout () () p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, B, t, _, hB, _, ht, _, _, hdvd⟩ :=
    (h (h := 1) (p := 3) (q := 3) (by decide) (by decide) (by decide)).1 equal_bases_dependent
  have hnum : t.num.toNat = 1 :=
    Nat.dvd_one.mp ((dvd_pow_self _ hB.ne').trans hdvd)
  have hnumInt : (t.num.toNat : ℤ) = t.num :=
    Int.toNat_of_nonneg (Rat.num_nonneg.2 (zero_le_one.trans ht.le))
  rw [hnum, Nat.cast_one] at hnumInt
  have hden : (1 : ℚ) ≤ t.den := by exact_mod_cast t.den_pos
  have hfrac := Rat.num_div_den t
  rw [← hnumInt, Int.cast_one] at hfrac
  apply not_le_of_gt ht
  rw [← hfrac]
  exact (div_le_iff₀ (zero_lt_one.trans_le hden)).2 (by simpa using hden)

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  exact ⟨(), 0, 1, by change (0 : ℕ) ≠ 2; decide⟩

def family : Registration arena (type_of% @clock_dependent_iff_common_base) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@clock_dependent_iff_common_base, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@clock_dependent_iff_common_base) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence.NumeratorDivisibility.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence.NumeratorDivisibility.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg",
        "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NumeratorDivisibility

namespace DependentForm

abbrev readoutSignature := signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization readoutSignature :=
  realize readoutSignature (fun _ hp q => omegaThree (hp.1 : ℝ) (hp.2 : ℝ) (q : ℝ))
    (fun e => nomatch e)

def rejected : Realization readoutSignature :=
  realize readoutSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := readoutSignature
  Law R := ∀ {h p q : ℕ}, 0 < h → 2 * h ≤ p → q ≤ 3 * h →
    omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0 →
    ¬ RationalPowerIndependent
      (3 * (p : ℚ) / ((p : ℚ) + q)) (2 * (p : ℚ) / ((p : ℚ) + h)) →
    log (4 / 3) * log 2 / log (2 * (p : ℝ)) ≤ |R.readout () ⟨h, p⟩ q|

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlog := log_pos (by norm_num : (1 : ℝ) < 3 / 2)
  have hne : omegaThree (1 : ℝ) 3 3 ≠ 0 := by
    norm_num [omegaThree]
    linarith only [hlog]
  have hbad := h (h := 1) (p := 3) (q := 3) (by decide) (by decide) (by decide)
    (by exact_mod_cast hne) equal_bases_dependent
  have hpos : 0 < log (4 / 3) * log 2 / log (2 * (3 : ℝ)) :=
    div_pos (mul_pos (log_pos (by norm_num)) (log_pos (by norm_num))) (log_pos (by norm_num))
  exact (not_le_of_gt hpos) (by simpa [rejected, realize] using hbad)

private theorem dependence : ObservationalDependence readoutSignature actual := by
  intro _
  refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
  simpa [actual, realize, omegaThree] using (log_pos (by norm_num : (1 : ℝ) < 2)).ne'

def family : Registration arena (type_of% @dependent_clock_abs_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dependent_clock_abs_lower, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dependent_clock_abs_lower) (Realization readoutSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence.DependentForm.unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence.DependentForm.family
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
    owner := `D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DependentForm

end Reg.D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
