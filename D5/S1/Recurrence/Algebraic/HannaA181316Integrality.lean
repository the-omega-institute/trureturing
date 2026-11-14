/- GID: D5/S1/Recurrence/Algebraic/HannaA181316Integrality
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaA181316Integrality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna's all-parameter q-integer formal exponential is integral. -/

/-
Admission candidate: open-problem-resolution, preregistration #30230.
The original quantifiers are all integers q>1 and all natural degrees.
The Dold-exponential criterion is reused without a positivity premise.
No global priority or exhaustive literature-search claim is made.
Declaration | proof_shape | live consumers
logarithm | definition | A, logarithm_eq
A | definition | claim, result
claim | definition | result
S | definition | geom_id, geom_factor, geom_prime_dvd, geom_power_dvd,
  sum_congruence, exponent_congruence, b, logarithm_eq
b | definition | b_dold, logarithm_eq, result
geom_id | bind-only | geom_factor, exponent_congruence, logarithm_eq
geom_factor | bind-only | geom_power_dvd
geom_prime_dvd | bind-only | geom_power_dvd
geom_power_dvd | content | b_dold
base_congruence | bind-only | sum_congruence
sum_congruence | bind-only | b_dold
exponent_congruence | content | b_dold
b_dold | content | result
logarithm_eq | bind-only | result
result | content | external source settlement
All bind-only helpers are consumed on the result's live derivation path.
No escape witness is claimed; admission_basis: open-problem-resolution.
Direct frozen owners:
D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality.integral_exp_of_dold,
logInput and Dold: module statement_id
sha256:2d31fedb86b5bee40c5e2a3f9556a8237f057c7fc2b4c4e007886a9d64fcb7d8.
D5/S1/Recurrence/Witt/HannaDiagonalGhostPowerIntegrality.fermat_lift:
original private owner in module statement_id
sha256:dc87d9e1c066581b845229f58331179ae8103aae9333d4be35d6b3aa51ffca2d.
The original theorem is exposed for base_congruence; its new public identity
requires canonical repinning after independent prefreeze review.
-/

import D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality
import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic

open Finset PowerSeries

namespace D5.S1.Recurrence.Algebraic.HannaA181316Integrality

noncomputable def logarithm (q : ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else
    ((q : ℚ) - 1) * (((q : ℚ) ^ n - 1) / ((q : ℚ) - 1)) ^ (n - 1) / (n : ℚ)

noncomputable def A (q : ℤ) : PowerSeries ℚ :=
  PowerSeries.subst (logarithm q) (PowerSeries.exp ℚ)

def claim : Prop :=
  ∀ q : ℤ, 1 < q → ∀ N : ℕ, ∃ z : ℤ, PowerSeries.coeff N (A q) = (z : ℚ)

private def S (q n : ℕ) : ℕ := ∑ i ∈ range n, q ^ i

private def b (q n : ℕ) : ℤ := ((q - 1) * S q n ^ (n - 1) : ℕ)

private theorem geom_id (q n : ℕ) :
    (S q n : ℤ) * ((q : ℤ) - 1) = (q : ℤ) ^ n - 1 := by
  simpa [S] using geom_sum_mul (q : ℤ) n

private theorem geom_factor (q n t : ℕ) (hq : 2 ≤ q) :
    S q (n * t) = S q n * S (q ^ n) t := by
  have he : (S q (n * t) : ℤ) = (S q n : ℤ) * S (q ^ n) t := by
    apply mul_right_cancel₀ (show (q : ℤ) - 1 ≠ 0 by omega)
    rw [geom_id]
    calc
      (q : ℤ) ^ (n * t) - 1 = ((q : ℤ) ^ n) ^ t - 1 := by rw [pow_mul]
      _ = (S (q ^ n) t : ℤ) * ((q : ℤ) ^ n - 1) := by
        simpa only [Nat.cast_pow] using (geom_id (q ^ n) t).symm
      _ = ((S q n : ℤ) * S (q ^ n) t) * ((q : ℤ) - 1) := by
        rw [← geom_id q n]; ring
  exact_mod_cast he

private theorem geom_prime_dvd (q n p : ℕ) (hq : 2 ≤ q) (hpq : p ∣ q - 1) :
    p ∣ S (q ^ n) p := by
  have hq1 : q ≡ 1 [MOD p] := (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).mpr hpq |>.symm
  have h := Nat.ModEq.sum (s := range p) (fun i _ => (hq1.pow n).pow i)
  have hz : S (q ^ n) p ≡ 0 [MOD p] :=
    (show S (q ^ n) p ≡ p [MOD p] by simpa [S] using h).trans
      (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
  exact Nat.modEq_zero_iff_dvd.mp hz

private theorem geom_power_dvd (q p a t : ℕ) (hq : 2 ≤ q) (hpq : p ∣ q - 1) :
    p ^ a ∣ S q (p ^ a * t) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have he : p ^ (a + 1) * t = (p ^ a * t) * p := by rw [pow_succ]; ring
    rw [he, geom_factor q _ p hq, pow_succ]
    exact Nat.mul_dvd_mul ih (geom_prime_dvd q _ p hq hpq)

private theorem base_congruence (q p n : ℕ) (hp : p.Prime) :
    q ^ (p * n) ≡ q ^ n [MOD p ^ (padicValNat p n + 1)] := by
  obtain ⟨t, ht⟩ := (pow_padicValNat_dvd : p ^ padicValNat p n ∣ n)
  have hf := Witt.HannaDiagonalGhostPowerIntegrality.fermat_lift p (padicValNat p n) hp
    ((q : ℤ) ^ t)
  rw [← pow_mul, ← pow_mul] at hf
  have he : t * p ^ (padicValNat p n + 1) = p * n := by
    calc
      t * p ^ (padicValNat p n + 1) = p * (p ^ padicValNat p n * t) := by rw [pow_succ]; ring
      _ = p * n := congrArg (p * ·) ht.symm
  have he' : t * p ^ padicValNat p n = n := (Nat.mul_comm _ _).trans ht.symm
  rw [he, he'] at hf
  exact Nat.modEq_iff_dvd.mpr (by simpa only [Nat.cast_pow, neg_sub] using dvd_neg.mpr hf)

private theorem sum_congruence (q p n : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (hpq : ¬ p ∣ q - 1) :
    S q (p * n) ≡ S q n [MOD p ^ (padicValNat p n + 1)] := by
  have hc : (p ^ (padicValNat p n + 1)).Coprime (q - 1) :=
    (hp.coprime_iff_not_dvd.mpr hpq).pow_left _
  apply Nat.ModEq.cancel_right_of_coprime hc
  have h := Nat.ModEq.sub_right (one_le_pow₀ (by omega : 1 ≤ q))
    (one_le_pow₀ (by omega : 1 ≤ q)) (base_congruence q p n hp)
  simpa only [S, geom_sum_mul_of_one_le (show 1 ≤ q by omega)] using h

private theorem exponent_congruence (q p n : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (hn : n ≠ 0) (hpq : ¬ p ∣ q - 1) :
    S q n ^ (p * n - 1) ≡ S q n ^ (n - 1) [MOD p ^ (padicValNat p n + 1)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  let a := padicValNat p n
  obtain ⟨t, ht⟩ := (pow_padicValNat_dvd : p ^ a ∣ n)
  by_cases hs : p ∣ S q n
  · have ht2 : 2 ≤ t := by
      have ht0 : t ≠ 0 := by intro h; simp [h] at ht; exact hn ht
      have ht1 : t ≠ 1 := by
        intro he
        have hn' : n = p ^ a := by simpa [he] using ht
        have hz : (S q n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hs
        have hg := congrArg (fun z : ℤ => (z : ZMod p)) (geom_id q n)
        have hf : (q : ZMod p) ^ n = q := by rw [hn']; exact ZMod.pow_card_pow _
        have hqz : (q : ZMod p) - 1 = 0 := by
          simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_one,
            Int.cast_pow, hz, zero_mul, hf] using hg.symm
        have hd : p ∣ q - 1 := (ZMod.natCast_eq_zero_iff _ _).mp (by
          rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]; exact hqz)
        exact hpq hd
      omega
    have hap : a < p ^ a := lt_of_lt_of_le (Nat.lt_two_pow_self (n := a)) (Nat.pow_le_pow_left hp.two_le a)
    have he : a + 1 ≤ n - 1 := by
      have hlarge : 2 * p ^ a ≤ n := by
        calc
          2 * p ^ a = p ^ a * 2 := Nat.mul_comm _ _
          _ ≤ p ^ a * t := Nat.mul_le_mul_left _ ht2
          _ = n := ht.symm
      omega
    have hd : p ^ (a + 1) ∣ S q n ^ (n - 1) :=
      (pow_dvd_pow_of_dvd hs _).trans (pow_dvd_pow _ he)
    have hle : n - 1 ≤ p * n - 1 := Nat.sub_le_sub_right (Nat.le_mul_of_pos_left n hp.pos) 1
    exact (Nat.modEq_zero_iff_dvd.mpr (hd.trans (pow_dvd_pow _ hle))).trans
      (Nat.modEq_zero_iff_dvd.mpr hd).symm
  · have hc : (S q n).Coprime (p ^ (a + 1)) :=
      ((hp.coprime_iff_not_dvd.mpr hs).pow_left _).symm
    have he := (Nat.ModEq.pow_totient hc).pow t
    rw [← pow_mul, Nat.totient_prime_pow_succ hp, one_pow] at he
    have hexp : p * n - 1 = (n - 1) + (p ^ a * (p - 1)) * t := by
      have hp1 : p = (p - 1) + 1 := by omega
      have hn1 : n = (n - 1) + 1 := by omega
      have heq : p * n = n + (p ^ a * (p - 1)) * t := by
        calc
          p * n = ((p - 1) + 1) * n := congrArg (· * n) hp1
          _ = n + (p - 1) * n := by ring
          _ = n + (p ^ a * (p - 1)) * t := by rw [ht]; ring
      omega
    rw [hexp]
    simpa only [← pow_add, mul_one] using he.mul_left (S q n ^ (n - 1))

private theorem b_dold (q : ℕ) (hq : 2 ≤ q) : DoldExponentialIntegrality.Dold (b q) := by
  intro p hp n hn
  haveI : Fact p.Prime := ⟨hp⟩
  let a := padicValNat p n
  change (p : ℤ) ^ (a + 1) ∣ b q (p * n) - b q n
  by_cases hpq : p ∣ q - 1
  · have hd (k : ℕ) (hk : 2 ≤ k) (hkn : p ^ a ∣ k) :
        p ^ (a + 1) ∣ (q - 1) * S q k ^ (k - 1) := by
      obtain ⟨t, rfl⟩ := hkn
      have hs := geom_power_dvd q p a t hq hpq
      by_cases ha : a = 0
      · simpa [ha] using dvd_mul_of_dvd_left hpq (S q (p ^ a * t) ^ (p ^ a * t - 1))
      · rw [pow_succ]
        have hh : p ^ a ∣ S q (p ^ a * t) ^ (p ^ a * t - 1) :=
          hs.trans (dvd_pow_self _ (by omega))
        exact (by simpa [mul_comm] using Nat.mul_dvd_mul hpq hh)
    by_cases ha : a = 0
    · have h1 : (p : ℤ) ∣ b q (p * n) := by unfold b; exact_mod_cast dvd_mul_of_dvd_left hpq (S q (p * n) ^ (p * n - 1))
      have h2 : (p : ℤ) ∣ b q n := by unfold b; exact_mod_cast dvd_mul_of_dvd_left hpq (S q n ^ (n - 1))
      simpa [ha] using dvd_sub h1 h2
    · have hn2 : 2 ≤ n := by
        have hpn : p ∣ n := (dvd_pow_self p ha).trans pow_padicValNat_dvd
        exact le_trans hp.two_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn)
      have h1 := hd n hn2 pow_padicValNat_dvd
      have h2 := hd (p * n) (by nlinarith [hp.two_le]) (dvd_mul_of_dvd_right pow_padicValNat_dvd p)
      have hi1 : (p : ℤ) ^ (a + 1) ∣ b q n := by unfold b; exact_mod_cast h1
      have hi2 : (p : ℤ) ^ (a + 1) ∣ b q (p * n) := by unfold b; exact_mod_cast h2
      exact dvd_sub hi2 hi1
  · have h := ((sum_congruence q p n hq hp hpq).pow (p * n - 1)).trans
      (exponent_congruence q p n hq hp hn hpq)
    have hi := Nat.modEq_iff_dvd.mp (h.mul_left (q - 1)).symm
    simpa only [b, Nat.cast_mul, Nat.cast_pow] using hi

private theorem logarithm_eq (q : ℕ) (hq : 2 ≤ q) :
    logarithm q = DoldExponentialIntegrality.logInput (b q) := by
  ext n
  simp only [logarithm, DoldExponentialIntegrality.logInput, coeff_mk, Int.cast_natCast]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]
    have hg : (S q n : ℚ) = ((q : ℚ) ^ n - 1) / ((q : ℚ) - 1) := by
      have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
      apply (eq_div_iff (by linarith : (q : ℚ) - 1 ≠ 0)).mpr
      exact_mod_cast geom_id q n
    rw [← hg]
    simp only [b, Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_pow,
      Int.cast_sub, Int.cast_one, Int.cast_natCast, Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_one]

/-- All allowed integer parameters and every ordinary formal coefficient. -/
theorem result : claim := by
  intro q hq
  have hnat : 2 ≤ q.toNat := by omega
  have he : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
  have hi := DoldExponentialIntegrality.integral_exp_of_dold (b q.toNat) (b_dold q.toNat hnat)
  rw [← logarithm_eq q.toNat hnat, he] at hi
  exact hi

end D5.S1.Recurrence.Algebraic.HannaA181316Integrality
