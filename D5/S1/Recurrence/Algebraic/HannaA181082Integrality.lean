/- GID: D5/S1/Recurrence/Algebraic/HannaA181082Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181082Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Integer coefficients of Hanna's OEIS A181082 formal exponential. -/

/-
Admission candidate: open-problem-resolution, preregistration #30033.
Every proof declaration is bind-only; escape_witness: none.
This is an unbounded theorem, not a finite computation or certified instance.
Definitions: logarithm -> A -> claim -> result; F82 is consumed by div82,
cong82 and result. Live proof consumers: div82 -> result,
exponent_congruence -> cong82 -> result. The only public theorem is result.
The direct frozen provider is HannaA181070Integrality, GID
D5/S1/Recurrence/Algebraic/HannaA181070Integrality, statement_id
sha256:3092db66acc6fd1d6f4354d8aefb1d52c3e934f2a8cbf9e86d1bed30e823810b.
Its integralGeneric, binomDiv, binomCong and literalBounded are applied directly.
No claim about global openness, priority or originality is made.
-/

import D5.S1.Recurrence.Algebraic.HannaA181070Integrality

open Finset PowerSeries
open D5.S1.Recurrence.Algebraic.HannaA181070Integrality

namespace D5.S1.Recurrence.Algebraic.HannaA181082Integrality

/-- The finite diagonal coefficients of the literal OEIS logarithm. -/
noncomputable def logarithm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (n + 1),
        if 0 < n ∧ n + k = m then
          ((n.choose k : ℕ) : ℚ) ^ (n + k) / (n : ℚ)
        else 0

/-- Ordinary formal exp(logarithm), with the inner series first in subst. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.subst logarithm (PowerSeries.exp ℚ)

/-- Integer images in every ordinary coefficient, including degree zero. -/
def claim : Prop :=
  ∀ m : ℕ, ∃ z : ℤ, PowerSeries.coeff m A = (z : ℚ)

private def F82 (n k : ℕ) : ℕ :=
  if n = 0 then 0 else (n.choose k) ^ (n + k)

private theorem div82 (n k : ℕ) (hn : n ≠ 0) : n ∣ k * F82 n k := by
  have ht : n + k = (n + k - 1) + 1 := by omega
  simp only [F82, if_neg hn]
  rw [ht, pow_succ', ← mul_assoc]
  exact dvd_mul_of_dvd_left (binomDiv n k) _

private theorem exponent_congruence (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    Nat.ModEq (p ^ (padicValNat p n + 1))
      ((n.choose k) ^ (p * (n + k))) ((n.choose k) ^ (n + k)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hb : p ∣ n.choose k
  · have ha : padicValNat p n + 1 ≤ n + k := by
      have := Nat.padicValNat_lt_self (p := p) hn
      omega
    have hz : p ^ (padicValNat p n + 1) ∣ (n.choose k) ^ (n + k) :=
      (pow_dvd_pow_of_dvd hb _).trans (pow_dvd_pow _ ha)
    have hle : n + k ≤ p * (n + k) := Nat.le_mul_of_pos_left _ hp.pos
    exact (Nat.modEq_zero_iff_dvd.mpr
      (hz.trans (pow_dvd_pow _ hle))).trans (Nat.modEq_zero_iff_dvd.mpr hz).symm
  · have hcop : p.Coprime (n.choose k) := hp.coprime_iff_not_dvd.mpr hb
    have hk : p ^ padicValNat p n ∣ k :=
      (hcop.pow_left _).dvd_of_dvd_mul_right (pow_padicValNat_dvd.trans (binomDiv n k))
    have ht : p ^ padicValNat p n ∣ n + k := dvd_add pow_padicValNat_dvd hk
    obtain ⟨u, hu⟩ := ht
    have hc : (n.choose k).Coprime (p ^ (padicValNat p n + 1)) :=
      (hcop.pow_left _).symm
    have he := (Nat.ModEq.pow_totient hc).pow u
    rw [← pow_mul, Nat.totient_prime_pow_succ hp, one_pow] at he
    have hexp : p * (n + k) = (n + k) + (p ^ padicValNat p n * (p - 1)) * u := by
      rw [hu]
      have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_prime hp).symm
      conv_lhs => lhs; rw [hp1]
      ring
    rw [hexp]
    simpa only [← pow_add, mul_one] using he.mul_left ((n.choose k) ^ (n + k))

private theorem cong82 (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (p : ℤ) ^ (padicValNat p n + 1) ∣ (F82 (p * n) (p * k) : ℤ) - F82 n k := by
  have hc := (binomCong p n k hp).pow (p * (n + k))
  have he := exponent_congruence p n k hp hn
  have h := Nat.modEq_iff_dvd.mp (hc.trans he).symm
  simpa only [F82, if_neg hn, if_neg (Nat.mul_ne_zero hp.ne_zero hn),
    Nat.mul_add, Nat.cast_pow] using h

/-- The complete original A181082 integrality assertion. -/
theorem result : claim := by
  have hl : logarithm = HannaA181070Integrality.L F82 := by
    ext m
    rw [logarithm, coeff_mk, ← literalBounded F82 (fun n k h => by
      by_cases hn : n = 0
      · simp [F82, hn]
      · simp [F82, hn, Nat.choose_eq_zero_of_lt h, show n + k ≠ 0 by omega]) m]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro k hk
    split_ifs with h
    · simp only [F82, if_neg (by omega : n ≠ 0), Nat.cast_pow]
    · rfl
  unfold claim A
  rw [hl]
  exact integralGeneric F82 div82 (fun p hp n k hn => cong82 p n k hp hn)

end D5.S1.Recurrence.Algebraic.HannaA181082Integrality
