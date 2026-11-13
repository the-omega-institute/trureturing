/- GID: D5/S1/Recurrence/Algebraic/HannaA181078Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181078Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every ordinary coefficient of Hanna's unbounded A181078 exponential is integral. -/

/-
Declaration inventory: name | proof_shape | consumers.
logarithm | definition | A, result
A | definition | claim
claim | definition | result
weight | definition | weight_divisibility, weight_congruence, result
weight_divisibility | bind-only | result
exponent_congruence | bind-only | weight_congruence
weight_congruence | bind-only | result
result | bind-only | external assertion OEIS A181078
Every theorem has escape_witness: none.
The only prospective admission basis is open-problem-resolution, source issue #30038.
The logarithm retains every k >= 0; a finite diagonal is not a support restriction.
-/

import D5.S1.Recurrence.Algebraic.HannaA181074Integrality

open Finset PowerSeries

namespace D5.S1.Recurrence.Algebraic.HannaA181078Integrality

/-- The literal unbounded double sum, collected coefficient by coefficient. -/
noncomputable def logarithm : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (m + 1),
        if 0 < n ∧ n + k = m then
          (((n + k - 1).choose k : ℕ) : ℚ) ^ (n + k - 1) / (n : ℚ)
        else 0

/-- Formal ordinary exponential: subst takes the inner series first. -/
noncomputable def A : PowerSeries ℚ :=
  PowerSeries.subst logarithm (PowerSeries.exp ℚ)

/-- Every ordinary coefficient, including the constant coefficient, is an integer. -/
def claim : Prop :=
  ∀ m : ℕ, ∃ z : ℤ, PowerSeries.coeff m A = (z : ℚ)

private def weight (n k : ℕ) : ℕ := ((n + k - 1).choose k) ^ (n + k - 1)

private theorem weight_divisibility (n k : ℕ) (hn : n ≠ 0) :
    n ∣ k * weight n k := by
  by_cases hs : n + k = 1
  · have he : n = 1 := by omega
    simp [he]
  · have hr : n + k - 1 = (n + k - 2) + 1 := by omega
    dsimp [weight]
    rw [hr, pow_succ']
    simpa only [← mul_assoc] using
      dvd_mul_of_dvd_left
        (HannaA181074Integrality.negbinomDiv n k hn)
        (((n + k - 1).choose k) ^ (n + k - 2))

private theorem exponent_congruence (p n k : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    Nat.ModEq (p ^ (padicValNat p n + 1))
      (((n + k - 1).choose k) ^ (p * n + p * k - 1))
      (((n + k - 1).choose k) ^ (n + k - 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let b := (n + k - 1).choose k
  change Nat.ModEq _ (b ^ _) (b ^ _)
  have hs : 1 ≤ n + k := by omega
  have hscale : n + k ≤ p * n + p * k := by
    simpa only [mul_add] using Nat.le_mul_of_pos_left (n + k) hp.pos
  by_cases hb : p ∣ b
  · have hn1 : n ≠ 1 := by
      intro he
      subst n
      have hb1 : p ∣ 1 := by simpa [b] using hb
      exact hp.not_dvd_one hb1
    have hk : k ≠ 0 := by
      intro he
      subst k
      have hb1 : p ∣ 1 := by simpa [b] using hb
      exact hp.not_dvd_one hb1
    have ha := Nat.padicValNat_lt_self (p := p) hn
    have hl : padicValNat p n + 1 ≤ n + k - 1 := by omega
    have hz : p ^ (padicValNat p n + 1) ∣ b ^ (n + k - 1) :=
      (pow_dvd_pow_of_dvd hb _).trans (pow_dvd_pow b hl)
    have hlarge : n + k - 1 ≤ p * n + p * k - 1 := by omega
    exact (Nat.modEq_zero_iff_dvd.mpr (hz.trans (pow_dvd_pow b hlarge))).trans
      (Nat.modEq_zero_iff_dvd.mpr hz).symm
  · have hcop : p.Coprime b := hp.coprime_iff_not_dvd.mpr hb
    have hkpow : p ^ padicValNat p n ∣ k :=
      (hcop.pow_left _).dvd_of_dvd_mul_right
        (pow_padicValNat_dvd.trans (HannaA181074Integrality.negbinomDiv n k hn))
    have hspow : p ^ padicValNat p n ∣ n + k :=
      dvd_add pow_padicValNat_dvd hkpow
    obtain ⟨t, ht⟩ := hspow
    have hc : b.Coprime (p ^ (padicValNat p n + 1)) := (hcop.pow_left _).symm
    have hu := (Nat.ModEq.pow_totient hc).pow t
    rw [← pow_mul, Nat.totient_prime_pow_succ hp, one_pow] at hu
    have hexp : p * n + p * k - 1 =
        (n + k - 1) + (p ^ padicValNat p n * (p - 1)) * t := by
      have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_le).symm
      calc
        p * n + p * k - 1 = p * (n + k) - 1 := by rw [mul_add]
        _ = ((p - 1) + 1) * (n + k) - 1 := by rw [← hp1]
        _ = (n + k - 1) + (p - 1) * (n + k) := by
          rw [add_mul, one_mul]
          omega
        _ = (n + k - 1) + (p ^ padicValNat p n * (p - 1)) * t := by
          rw [ht]
          ring
    rw [hexp]
    simpa only [← pow_add, mul_one] using hu.mul_left (b ^ (n + k - 1))

private theorem weight_congruence (p : ℕ) (hp : p.Prime) (n k : ℕ) (hn : n ≠ 0) :
    (p : ℤ) ^ (padicValNat p n + 1) ∣
      (weight (p * n) (p * k) : ℤ) - weight n k := by
  have hc := (HannaA181074Integrality.negbinomCong p n k hp hn).pow
    (p * n + p * k - 1)
  have he := exponent_congruence p n k hp hn
  have h := Nat.modEq_iff_dvd.mp (hc.trans he).symm
  simpa only [weight, Nat.cast_pow] using h

theorem result : claim := by
  have hl : logarithm = HannaA181070Integrality.L weight := by
    ext m
    simpa only [logarithm, coeff_mk, weight, Nat.cast_pow] using
      HannaA181070Integrality.literalUnbounded weight m
  unfold claim A
  rw [hl]
  exact HannaA181070Integrality.integralGeneric weight
    weight_divisibility weight_congruence

end D5.S1.Recurrence.Algebraic.HannaA181078Integrality
