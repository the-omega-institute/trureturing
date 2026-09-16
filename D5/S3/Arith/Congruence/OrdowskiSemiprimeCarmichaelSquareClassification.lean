/- GID: D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordowski's A306270 semiprime classification via Carmichael exponents. -/

import Mathlib.NumberTheory.ArithmeticFunction.Carmichael

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.OrdowskiSemiprimeCarmichaelSquareClassification

/-- Membership in A306270: composite `k` such that every `b` coprime to `k`
satisfies `b^(k(k-1)) ≡ 1 (mod k^2)`. -/
def mem (k : ℕ) : Prop :=
  ¬k.Prime ∧ 1 < k ∧
    ∀ b, Nat.Coprime b k → b ^ (k * (k - 1)) ≡ 1 [MOD k ^ 2]

/-- Ordowski's classification: if `k = p*q > 4` is a semiprime in A306270
with `p ≤ q`, then `q = p^2-p+1`, so `k` belongs to A190275. -/
theorem result (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (h4 : 4 < p * q) (hk : mem (p * q)) : q = p ^ 2 - p + 1 := by
  open ArithmeticFunction in
    rcases hk with ⟨_, _, hpow⟩
    have hpq_ne : p * q ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
    have hp_two : 2 ≤ p := hp.two_le
    have hq_two : 2 ≤ q := hq.two_le
    have hcarm : carmichael ((p * q) ^ 2) ∣ (p * q) * (p * q - 1) := by
      let _ : NeZero ((p * q) ^ 2) := ⟨pow_ne_zero 2 hpq_ne⟩
      rw [carmichael_eq_exponent (pow_ne_zero 2 hpq_ne)]
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro u
      have hu_coprime_sq := ZMod.val_coe_unit_coprime u
      have hu_coprime : Nat.Coprime (u : ZMod ((p * q) ^ 2)).val (p * q) :=
        hu_coprime_sq.of_dvd_right (by
          rw [pow_two]
          exact Nat.dvd_mul_right (p * q) (p * q))
      apply Units.ext
      change ((u : ZMod ((p * q) ^ 2)) ^ ((p * q) * (p * q - 1))) = 1
      rw [← ZMod.natCast_zmod_val (u : ZMod ((p * q) ^ 2)), ← Nat.cast_pow]
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ _ _).2
        (hpow (u : ZMod ((p * q) ^ 2)).val hu_coprime)
    have hcarm_sq : ∀ r : ℕ, r.Prime → carmichael (r ^ 2) = r * (r - 1) := by
      intro r hr
      by_cases hr2 : r = 2
      · subst r
        rw [carmichael_two_pow_of_le_two (n := 2) (by omega)]
        norm_num
      · rw [carmichael_pow_of_prime_ne_two 2 hr hr2]
        simpa using Nat.totient_prime_pow_succ hr 1
    have hp_sq_dvd : p ^ 2 ∣ (p * q) ^ 2 := by
      rw [mul_pow]
      exact Nat.dvd_mul_right (p ^ 2) (q ^ 2)
    have hq_sq_dvd : q ^ 2 ∣ (p * q) ^ 2 := by
      rw [mul_pow, mul_comm]
      exact Nat.dvd_mul_right (q ^ 2) (p ^ 2)
    have hp_div : p * (p - 1) ∣ (p * q) * (p * q - 1) := by
      rw [← hcarm_sq p hp]
      exact (carmichael_dvd hp_sq_dvd).trans hcarm
    have hq_div : q * (q - 1) ∣ (p * q) * (p * q - 1) := by
      rw [← hcarm_sq q hq]
      exact (carmichael_dvd hq_sq_dvd).trans hcarm
    have hp1_div : p - 1 ∣ q * (p * q - 1) := by
      apply (Nat.mul_dvd_mul_iff_left hp.pos).mp
      simpa [mul_assoc] using hp_div
    have hq1_div : q - 1 ∣ p * (p * q - 1) := by
      apply (Nat.mul_dvd_mul_iff_left hq.pos).mp
      simpa [mul_assoc, mul_comm, mul_left_comm] using hq_div
    have hp_lt_q : p < q := by
      apply hpq.lt_of_ne
      intro hpq_eq
      subst q
      have hp_ne_two : p ≠ 2 := by
        intro hp2
        subst p
        norm_num at h4
      have hcarm_four : carmichael (p ^ 4) = p ^ 3 * (p - 1) := by
        rw [carmichael_pow_of_prime_ne_two 4 hp hp_ne_two]
        simpa using Nat.totient_prime_pow_succ hp 3
      have hp_four_div : p ^ 3 * (p - 1) ∣ p ^ 2 * (p ^ 2 - 1) := by
        rw [← hcarm_four]
        simpa [pow_succ, mul_assoc] using hcarm
      have hp_mul_div : p * (p - 1) ∣ p ^ 2 - 1 := by
        apply (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos 2)).mp
        simpa [pow_succ, mul_assoc] using hp_four_div
      have hp_dvd_pred : p ∣ p ^ 2 - 1 :=
        (Nat.dvd_mul_right p (p - 1)).trans hp_mul_div
      have hp_dvd_one : p ∣ 1 := by
        have hsub := Nat.dvd_sub (dvd_pow_self p (by decide : 2 ≠ 0)) hp_dvd_pred
        have hone : 1 ≤ p ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hp.ne_zero)
        rw [Nat.sub_sub_self hone] at hsub
        exact hsub
      exact hp.not_dvd_one hp_dvd_one
    by_cases hp2 : p = 2
    · subst p
      have htwo : q - 1 ∣ 2 := by
        have hmultiple : q - 1 ∣ 4 * (q - 1) := Nat.dvd_mul_left (q - 1) 4
        have hdifference := Nat.dvd_sub hq1_div hmultiple
        convert hdifference using 1
        all_goals omega
      have hq_le : q - 1 ≤ 2 := Nat.le_of_dvd (by omega) htwo
      norm_num [pow_two]
      omega
    · have hp1_coprime_q : Nat.Coprime (p - 1) q := by
        apply (hq.coprime_iff_not_dvd.mpr ?_).symm
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      have hp1_div_pred : p - 1 ∣ p * q - 1 :=
        hp1_coprime_q.dvd_of_dvd_mul_left hp1_div
      have hp1_div_q1 : p - 1 ∣ q - 1 := by
        have hmultiple : p - 1 ∣ q * (p - 1) := Nat.dvd_mul_left (p - 1) q
        have hdifference := Nat.dvd_sub hp1_div_pred hmultiple
        have hq_le_pq : q ≤ p * q := Nat.le_mul_of_pos_left q hp.pos
        convert hdifference using 1
        all_goals
          simp only [Nat.mul_sub_left_distrib, mul_one, mul_comm q p]
          omega
      have hq1_div_pp1 : q - 1 ∣ p * (p - 1) := by
        have hmultiple : q - 1 ∣ p ^ 2 * (q - 1) := Nat.dvd_mul_left (q - 1) (p ^ 2)
        have hdifference := Nat.dvd_sub hq1_div hmultiple
        have hp_le_sq : p ≤ p ^ 2 := by
          simpa [pow_two] using Nat.le_mul_of_pos_right p hp.pos
        have hp_sq_le : p ^ 2 ≤ p ^ 2 * q := Nat.le_mul_of_pos_right (p ^ 2) hq.pos
        convert hdifference using 1
        all_goals
          simp only [Nat.mul_sub_left_distrib, mul_one, pow_two]
          ring_nf
          omega
      obtain ⟨t, ht⟩ := hp1_div_q1
      have ht_ne_zero : t ≠ 0 := by
        intro ht0
        simp [ht0] at ht
        omega
      have ht_ne_one : t ≠ 1 := by
        intro ht1
        simp [ht1] at ht
        omega
      have ht_dvd_p : t ∣ p := by
        apply (Nat.mul_dvd_mul_iff_left (by omega : 0 < p - 1)).mp
        simpa [ht, mul_comm] using hq1_div_pp1
      have ht_eq_p : t = p := by
        rcases (Nat.dvd_prime hp).mp ht_dvd_p with ht1 | htp
        · exact (ht_ne_one ht1).elim
        · exact htp
      rw [ht_eq_p] at ht
      simp only [Nat.sub_mul, one_mul] at ht
      simp [pow_two]
      omega

end D5.S3.Arith.Congruence.OrdowskiSemiprimeCarmichaelSquareClassification
