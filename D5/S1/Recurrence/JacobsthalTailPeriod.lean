/- GID: D5/S1/Recurrence/JacobsthalTailPeriod
   generality: G
   mirror-B: none(waiver:actual-noninvertible-recurrence)
   mirror-E: none(waiver:all-tail-starts-and-all-shifts)
   anchors: []
   digest: An exact integer divisibility criterion describes every Jacobsthal tail period. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.JacobsthalTailPeriod

/-- The original second-order recurrence, with its original two initial terms. -/
def jacobsthal : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n

/-- A shift valid at every index from N onwards. Positivity of a period is separate. -/
def PeriodFrom (m N t : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → (m : ℤ) ∣ jacobsthal (n + t) - jacobsthal n

/-- Explicit source identification; the first-order identity is not used as a new definition. -/
theorem defining_relation :
    jacobsthal 0 = 0 ∧ jacobsthal 1 = 1 ∧
      ∀ n : ℕ, jacobsthal (n + 2) = jacobsthal (n + 1) + 2 * jacobsthal n :=
  ⟨rfl, rfl, fun _ => rfl⟩

private lemma first_order (n : ℕ) :
    jacobsthal (n + 1) = 2 * jacobsthal n + (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num [jacobsthal]
  | succ n ih =>
      change jacobsthal (n + 2) = 2 * jacobsthal (n + 1) + (-1 : ℤ) ^ (n + 1)
      rw [jacobsthal, pow_succ]
      nlinarith only [ih]

private lemma integer_binet (n : ℕ) :
    3 * jacobsthal n = (2 : ℤ) ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero => norm_num [jacobsthal]
  | succ n ih =>
      rw [first_order, pow_succ, pow_succ]
      nlinarith only [ih]

private lemma even_shift (n t : ℕ) (ht : Even t) :
    jacobsthal (n + t) - jacobsthal n = (2 : ℤ) ^ n * jacobsthal t := by
  have hnt := integer_binet (n + t)
  have hn := integer_binet n
  have hmul := congrArg (fun z : ℤ => (2 : ℤ) ^ n * z) (integer_binet t)
  rw [pow_add, pow_add, ht.neg_one_pow, mul_one] at hnt
  rw [ht.neg_one_pow] at hmul
  nlinarith only [hnt, hn, hmul]

private lemma tail_even (m N t : ℕ) (hm : 2 < m) (h : PeriodFrom m N t) : Even t := by
  have h0 := h N (le_refl N)
  have h1 := h (N + 1) (by omega)
  have hD := dvd_sub h1 (dvd_mul_of_dvd_right h0 (2 : ℤ))
  have he :
      (jacobsthal (N + 1 + t) - jacobsthal (N + 1)) -
          2 * (jacobsthal (N + t) - jacobsthal N) =
        (-1 : ℤ) ^ N * ((-1 : ℤ) ^ t - 1) := by
    rw [show N + 1 + t = (N + t) + 1 by omega, first_order, first_order, pow_add]
    ring
  rw [he] at hD
  have hsign : (m : ℤ) ∣ (-1 : ℤ) ^ t - 1 := by
    rcases Nat.even_or_odd N with hN | hN
    · simpa only [hN.neg_one_pow, one_mul] using hD
    · have hh : (m : ℤ) ∣ -((-1 : ℤ) ^ t - 1) := by
        simpa only [hN.neg_one_pow, neg_one_mul] using hD
      exact dvd_neg.mp hh
  rcases Nat.even_or_odd t with ht | ht
  · exact ht
  · have hneg : (m : ℤ) ∣ (-2 : ℤ) := by
      simpa only [ht.neg_one_pow, show (-1 : ℤ) - 1 = -2 by norm_num] using hsign
    have hpos : (m : ℤ) ∣ (2 : ℤ) := dvd_neg.mp hneg
    have hnat : m ∣ 2 := by exact_mod_cast hpos
    have hle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hnat
    omega

/-- Complete criterion at an arbitrary tail start. The modulus-three factor in Binet
is never cancelled modulo a multiple of three; all division is avoided here. -/
theorem period_from_iff (m N t : ℕ) (hm : 2 < m) :
    PeriodFrom m N t ↔ Even t ∧ (m : ℤ) ∣ (2 : ℤ) ^ N * jacobsthal t := by
  constructor
  · intro h
    have ht := tail_even m N t hm h
    refine ⟨ht, ?_⟩
    simpa only [even_shift N t ht] using h N (le_refl N)
  · rintro ⟨ht, hdiv⟩ n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [even_shift _ _ ht, pow_add]
    convert dvd_mul_of_dvd_right hdiv ((2 : ℤ) ^ k) using 1 <;> ring

private lemma not_two_dvd_positive (t : ℕ) (ht : 0 < t) :
    ¬ (2 : ℤ) ∣ jacobsthal t := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hz : (jacobsthal (n + 1) : ZMod 2) = 1 := by
    rw [first_order]
    push_cast
    norm_num
  intro hd
  have hzero : (jacobsthal (n + 1) : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hd
  rw [hzero] at hz
  norm_num at hz

/-- Every even modulus has no positive pure period from index zero. This includes m=2. -/
theorem no_positive_pure_period_even (m t : ℕ) (hm : Even m) (ht : 0 < t) :
    ¬ PeriodFrom m 0 t := by
  intro h
  have hJ : (m : ℤ) ∣ jacobsthal t := by simpa [jacobsthal] using h 0 (le_refl 0)
  have htwo : (2 : ℤ) ∣ (m : ℤ) := by
    obtain ⟨k, hk⟩ := hm
    refine ⟨(k : ℤ), ?_⟩
    exact_mod_cast (show m = 2 * k by omega)
  exact not_two_dvd_positive t ht (dvd_trans htwo hJ)

end D5.S1.Recurrence.JacobsthalTailPeriod
