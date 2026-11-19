import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.MobiusDyadicShellLower
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import Reg.Support.SingleDependentReadout

/-! Source-bound readout of the signed Möbius shell energy at the witness index. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.MobiusDyadicEnergy
  (mobiusDyadicDifference mobiusDyadicShellEnergy)
open _root_.D5.S3.Weil.Mertens.MobiusDyadicShellLower
  (exists_mobiusDyadicShellEnergy_ge_of_zero)
open _root_.D5.S3.Weil.ZeroSum (IsNontrivialZero)
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (exists_nontrivial_zero_re_ge_half mobiusPartialSum)

namespace Reg.D5.S3.Weil.Mertens.MobiusDyadicShellLower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ k => mobiusDyadicShellEnergy k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ρ : ℂ}, IsNontrivialZero ρ → (1 / 2 : ℝ) ≤ ρ.re →
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ k : ℕ, M ≤ k ∧
      c * ((2 : ℝ) ^ (2 * ρ.re - 1)) ^ k ≤ R.readout () () k

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, hρ, hh⟩ := exists_nontrivial_zero_re_ge_half
  obtain ⟨c, hc, ht⟩ := h hρ hh
  obtain ⟨k, _, hk⟩ := ht 0
  change c * ((2 : ℝ) ^ (2 * ρ.re - 1)) ^ k ≤ 0 at hk
  have hq : 0 < (2 : ℝ) ^ (2 * ρ.re - 1) := Real.rpow_pos_of_pos (by norm_num) _
  exact (not_le_of_gt (mul_pos hc (pow_pos hq k))) hk

private def weightedAt (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius m : ℝ) / (m : ℝ)

private theorem weightedAt_succ (n : ℕ) :
    weightedAt (n + 1) = weightedAt n +
      (ArithmeticFunction.moebius (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  unfold weightedAt
  rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]

-- Both natural floors are constant on the left-closed half-step.
private theorem shellPiece {a b : ℝ} (n m : ℕ) (hlen : b - a = 1 / 2)
    (hlo : (n : ℝ) ≤ a) (hhi : b ≤ (n : ℝ) + 1)
    (hlo₂ : (m : ℝ) ≤ 2 * a) (hhi₂ : 2 * b ≤ (m : ℝ) + 1) :
    IntervalIntegrable (fun x => mobiusDyadicDifference x ^ 2) volume a b ∧
      (∫ x in a..b, mobiusDyadicDifference x ^ 2) =
        (weightedAt n - weightedAt m) ^ 2 / 2 := by
  have hab : a ≤ b := by linarith only [hlen]
  let value := (weightedAt n - weightedAt m) ^ 2
  have heq : EqOn (fun x => mobiusDyadicDifference x ^ 2) (fun _ => value) (Ico a b) := by
    intro x hx
    have hxn : (n : ℝ) ≤ x := hlo.trans hx.1
    have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hxn
    have hfloor : ⌊x⌋₊ = n :=
      (Nat.floor_eq_iff hx0).2 ⟨hxn, hx.2.trans_le hhi⟩
    have hfloor₂ : ⌊2 * x⌋₊ = m :=
      (Nat.floor_eq_iff (mul_nonneg (by norm_num) hx0)).2
        ⟨by linarith only [hlo₂, hx.1], by linarith only [hhi₂, hx.2]⟩
    change mobiusDyadicDifference x ^ 2 = value
    dsimp only [value, mobiusDyadicDifference, mobiusPartialSum, weightedAt]
    rw [hfloor, hfloor₂]
  have hconst : IntervalIntegrable (fun _ : ℝ => value) volume a b := intervalIntegrable_const
  refine ⟨(intervalIntegrable_iff_integrableOn_Ico_of_le hab).2
    (((intervalIntegrable_iff_integrableOn_Ico_of_le hab).1 hconst).congr_fun
      heq.symm measurableSet_Ico), ?_⟩
  calc
    (∫ x in a..b, mobiusDyadicDifference x ^ 2) =
        ∫ x in Ico a b, mobiusDyadicDifference x ^ 2 := by
      rw [intervalIntegral.integral_of_le hab, integral_Ico_eq_integral_Ioc]
    _ = ∫ _ in Ico a b, value := setIntegral_congr_fun measurableSet_Ico heq
    _ = ∫ _ in a..b, value := by
      rw [intervalIntegral.integral_of_le hab, integral_Ico_eq_integral_Ioc]
    _ = (weightedAt n - weightedAt m) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen]
      dsimp only [value]
      ring

private theorem actual_dependence : ObservationalDependence signature actual := by
  have hμ₂ : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hμ₃ : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have hμ₄ : ArithmeticFunction.moebius 4 = 0 := by
    have h := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by decide : (2 : ℕ) ≠ 0)
    simpa using h
  have hμ₅ : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have hμ₆ : ArithmeticFunction.moebius 6 = 1 := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.gcd 2 3 = 1 by decide)
    change ArithmeticFunction.moebius 6 =
      ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius 3 at h
    simpa [hμ₂, hμ₃] using h
  have hμ₇ : ArithmeticFunction.moebius 7 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have h₁ : weightedAt 1 = 1 := by
    rw [weightedAt, Finset.Icc_self, Finset.sum_singleton]
    norm_num [ArithmeticFunction.moebius_apply_one]
  have h₂ : weightedAt 2 = 1 / 2 := by
    have h := weightedAt_succ 1
    norm_num [h₁, hμ₂] at h ⊢ <;> exact h
  have h₃ : weightedAt 3 = 1 / 6 := by
    have h := weightedAt_succ 2
    norm_num [h₂, hμ₃] at h ⊢ <;> exact h
  have h₄ : weightedAt 4 = 1 / 6 := by
    have h := weightedAt_succ 3
    norm_num [h₃, hμ₄] at h ⊢ <;> exact h
  have h₅ : weightedAt 5 = -(1 / 30) := by
    have h := weightedAt_succ 4
    norm_num [h₄, hμ₅] at h ⊢ <;> exact h
  have h₆ : weightedAt 6 = 2 / 15 := by
    have h := weightedAt_succ 5
    norm_num [h₅, hμ₆] at h ⊢ <;> exact h
  have h₇ : weightedAt 7 = -(1 / 105) := by
    have h := weightedAt_succ 6
    norm_num [h₆, hμ₇] at h ⊢ <;> exact h
  have h12 := shellPiece (a := 1) (b := 3 / 2) 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 := shellPiece (a := 3 / 2) (b := 2) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h24 := shellPiece (a := 2) (b := 5 / 2) 2 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h25 := shellPiece (a := 5 / 2) (b := 3) 2 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h36 := shellPiece (a := 3) (b := 7 / 2) 3 6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h37 := shellPiece (a := 7 / 2) (b := 4) 3 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hzero : mobiusDyadicShellEnergy 0 = 17 / 36 := by
    unfold mobiusDyadicShellEnergy
    norm_num
    rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
      ← intervalIntegral.integral_add_adjacent_intervals h12.1 h13.1, h12.2, h13.2]
    norm_num [h₁, h₂, h₃]
  have hone : mobiusDyadicShellEnergy 1 = 9431 / 44100 := by
    unfold mobiusDyadicShellEnergy
    norm_num
    rw [← intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4),
      ← intervalIntegral.integral_add_adjacent_intervals ((h24.1.trans h25.1).trans h36.1) h37.1,
      ← intervalIntegral.integral_add_adjacent_intervals (h24.1.trans h25.1) h36.1,
      ← intervalIntegral.integral_add_adjacent_intervals h24.1 h25.1,
      h24.2, h25.2, h36.2, h37.2]
    norm_num [h₂, h₃, h₄, h₅, h₆, h₇]
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change mobiusDyadicShellEnergy 0 ≠ mobiusDyadicShellEnergy 1
  norm_num [hzero, hone]

def evidence : Registration arena (type_of% @exists_mobiusDyadicShellEnergy_ge_of_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_mobiusDyadicShellEnergy_ge_of_zero, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_mobiusDyadicShellEnergy_ge_of_zero) (Realization signature) (ℕ → ℝ) Unit where
  unitName :=
    `D5.S3.Weil.Mertens.MobiusDyadicShellLower.exists_mobiusDyadicShellEnergy_ge_of_zero.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.MobiusDyadicShellLower.evidence
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
    owner := `D5.S3.Weil.Mertens.MobiusDyadicShellLower
    definition := none
    coordinates := #[]
    -- The final inequality's right operand in the saved statement-v1 material.
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.MobiusDyadicShellLower
