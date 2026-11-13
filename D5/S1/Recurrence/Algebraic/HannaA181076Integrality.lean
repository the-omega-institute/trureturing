/- GID: D5/S1/Recurrence/Algebraic/HannaA181076Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181076Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every ordinary coefficient of Hanna's OEIS A181076 exponential is an integer. -/

import D5.S1.Recurrence.Algebraic.HannaA181074Integrality
import D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality

/-! The source logarithm has a locally finite diagonal in every degree. -/

namespace D5.S1.Recurrence.Algebraic.HannaA181076Integrality

open Finset PowerSeries
open HannaA181070Integrality

/-- The locally finite logarithm of the source ordinary generating function. -/
noncomputable def logarithm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (m + 1),
      if 0 < n ∧ n + k = m then
        (((n + k - 1).choose k : ℕ) : ℚ) ^ n / (n : ℚ)
      else 0

/-- The ordinary formal exponential of the zero-constant logarithm. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.subst logarithm (PowerSeries.exp ℚ)

/-- Integrality in every natural degree, including degree zero. -/
def claim : Prop :=
  ∀ m : ℕ, ∃ z : ℤ, PowerSeries.coeff m A = (z : ℚ)

private def F (n k : ℕ) : ℕ :=
  if n = 0 then 0 else ((n + k - 1).choose k) ^ n

theorem result : claim := by
  have hF : ∀ n k, n ≠ 0 → n ∣ k * F n k := by
    intro n k hn
    simpa only [F, ite_eq_right hn, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using
      divPower (fun n k => (n + k - 1).choose k) (fun n _ => n - 1)
        HannaA181074Integrality.negbinomDiv n k hn
  have hcong : ∀ p : ℕ, p.Prime → ∀ n k : ℕ, n ≠ 0 →
      (p : ℤ) ^ (padicValNat p n + 1) ∣ (F (p * n) (p * k) : ℤ) - F n k := by
    intro p hp n k hn
    let : Fact p.Prime := ⟨hp⟩
    let b : ℤ := ((n + k - 1).choose k : ℕ)
    have hc := Nat.modEq_iff_dvd.mp
      ((HannaA181074Integrality.negbinomCong p n k hp hn).pow (p * n)).symm
    have hf : (p : ℤ) ∣ b ^ p - b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      simp only [Int.cast_sub, Int.cast_pow, ZMod.pow_card, sub_self]
    have he := HannaSelfSubstitutionIntegrality.power_lift p hf n
    rw [← pow_mul] at he
    have hc' : (p : ℤ) ^ (padicValNat p n + 1) ∣
        (((p * n + p * k - 1).choose (p * k) : ℕ) : ℤ) ^ (p * n) - b ^ (p * n) := by
      simpa only [Nat.cast_pow, b] using hc
    have h := dvd_add hc' he
    simpa only [F, ite_eq_right hn, ite_eq_right (Nat.mul_ne_zero hp.ne_zero hn), Nat.cast_pow,
      b, sub_add_sub_cancel] using h
  have hl : logarithm = L F := by
    ext m
    rw [← literalUnbounded F m]
    simp only [logarithm, coeff_mk]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · simp only [F, ite_eq_right (Nat.ne_of_gt h.1), Nat.cast_pow]
    · rfl
  have hi : HannaLogarithmicPowerClosure.IntegralSeries A := by
    unfold A
    rw [hl]
    exact integralGeneric F hF hcong
  have hz : constantCoeff logarithm = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logarithm]
  have ha : coeff 0 A = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, A, constantCoeff_eq,
      constantCoeff_subst_of_constantCoeff_zero hz, constantCoeff_exp]
    simp
  intro m
  cases m with
  | zero => exact ⟨1, by simpa only [Int.cast_one] using ha⟩
  | succ m => exact hi (m + 1)

end D5.S1.Recurrence.Algebraic.HannaA181076Integrality
