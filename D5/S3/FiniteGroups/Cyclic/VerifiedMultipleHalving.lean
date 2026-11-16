/- GID: D5/S3/FiniteGroups/Cyclic/VerifiedMultipleHalving
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/VerifiedMultipleHalving
   mirror-E: none(waiver:general-monoid-recursion)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Executable halving reaches an odd order quotient and preserves half-powers at even order. -/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-! A returning exponent is reduced using only the element and decidable power tests. -/

set_option autoImplicit false

namespace ShorHalving

/-- The executable guard uses only the supplied element and exponent. -/
def stripTwos {G : Type*} [Monoid G] [DecidableEq G] (x : G) (m : ℕ) : ℕ :=
  if h : 0 < m ∧ m % 2 = 0 ∧ x ^ (m / 2) = 1 then
    stripTwos x (m / 2)
  else m
termination_by m
decreasing_by exact Nat.div_lt_self h.1 (by decide)

/-- Halving removes only powers of two, reaches an odd order quotient, and
preserves the true-order half-power when the true order is even. -/
theorem stripTwos_correct {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (m : ℕ) (hm : 0 < m) (hxm : x ^ m = 1) :
    let M := stripTwos x m
    0 < M ∧ M ∣ m ∧ x ^ M = 1 ∧
      (∃ k : ℕ, m = 2 ^ k * M) ∧ Odd (M / orderOf x) ∧
      (Even (orderOf x) → Even M ∧ x ^ (M / 2) = x ^ (orderOf x / 2)) ∧
      (Odd (orderOf x) → Odd M) := by
  have run : ∀ n : ℕ, 0 < n → x ^ n = 1 →
      0 < stripTwos x n ∧ (∃ k : ℕ, n = 2 ^ k * stripTwos x n) ∧
        x ^ stripTwos x n = 1 ∧ Odd (stripTwos x n / orderOf x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hxn
      by_cases hs : 0 < n ∧ n % 2 = 0 ∧ x ^ (n / 2) = 1
      · have hlt : n / 2 < n := Nat.div_lt_self hn (by decide)
        have hpos : 0 < n / 2 := by omega
        obtain ⟨hp, ⟨k, hk⟩, hpow, hodd⟩ := ih (n / 2) hlt hpos hs.2.2
        have heq : stripTwos x n = stripTwos x (n / 2) := by
          rw [stripTwos, dite_eq_left hs]
        rw [heq]
        refine ⟨hp, ⟨k + 1, ?_⟩, hpow, hodd⟩
        calc
          n = 2 * (n / 2) := by omega
          _ = 2 * (2 ^ k * stripTwos x (n / 2)) := congrArg (fun q : ℕ => 2 * q) hk
          _ = 2 ^ (k + 1) * stripTwos x (n / 2) := by rw [pow_succ]; ring
      · have heq : stripTwos x n = n := by
          rw [stripTwos, dite_eq_right hs]
        rw [heq]
        refine ⟨hn, ⟨0, by simp⟩, hxn, Nat.not_even_iff_odd.mp ?_⟩
        rintro ⟨k, hk⟩
        have hdvd : orderOf x ∣ n := orderOf_dvd_iff_pow_eq_one.mpr hxn
        have hn2 : n = 2 * (orderOf x * k) := by
          calc
            n = n / orderOf x * orderOf x := (Nat.div_mul_cancel hdvd).symm
            _ = 2 * (orderOf x * k) := by rw [hk]; ring
        have hhalf : n / 2 = orderOf x * k := by omega
        apply hs
        refine ⟨hn, by omega, ?_⟩
        rw [hhalf, pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨hpos, ⟨k, hk⟩, hpow, hodd⟩ := run m hm hxm
  dsimp only
  have hdvd : orderOf x ∣ stripTwos x m := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hfactor : stripTwos x m = orderOf x * (stripTwos x m / orderOf x) := by
    simpa only [Nat.mul_comm] using (Nat.div_mul_cancel hdvd).symm
  refine ⟨hpos, ⟨2 ^ k, by simpa only [Nat.mul_comm] using hk⟩,
    hpow, ⟨k, hk⟩, hodd, ?_, ?_⟩
  · intro heven
    constructor
    · rw [hfactor]
      exact heven.mul_right _
    · obtain ⟨t, ht⟩ := hodd
      have heq : stripTwos x m = 2 * (orderOf x * t) + orderOf x := by
        rw [hfactor, ht]
        ring
      have hrmod : orderOf x % 2 = 0 := by
        obtain ⟨s, hs⟩ := heven
        omega
      have hhalf : stripTwos x m / 2 = orderOf x * t + orderOf x / 2 := by omega
      rw [hhalf, pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
  · intro hoddOrder
    rw [hfactor]
    exact hoddOrder.mul hodd

end ShorHalving
