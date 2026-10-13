/- GID: D5/S3/Arith/GoldenResource/GoldenCell5040SmallPrimeExclusion
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenCell5040SmallPrimeExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: none
   digest: Generic period obstruction plus the 5040 residual-prime exclusion below 47. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion

/-- A period-one residue at a divisor is incompatible with a distinct target
residue in any power congruence.  This is the reusable obstruction behind the
5040 residual-prime exclusion. -/
theorem modEq_period_not_dvd {a r n p k : ℕ}
    (hmod : Nat.ModEq n (a ^ n) r)
    (hperiod : Nat.ModEq p (a ^ k) 1) (hk : k ∣ n)
    (hbad : ¬ Nat.ModEq p r 1) : ¬ p ∣ n := by
  intro hd
  have hpow : Nat.ModEq p (a ^ n) 1 := by
    obtain ⟨t, rfl⟩ := hk
    simpa only [pow_mul, one_pow] using hperiod.pow t
  exact hbad ((hmod.of_dvd hd).symm.trans hpow)

private theorem excluded_twenty_three {n : ℕ}
    (hmod : Nat.ModEq n (3 ^ n) 2241) : ¬ 23 ∣ n := by
  intro hd
  have hres : (3 : ZMod 23) ^ n = 2241 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff (3 ^ n) 2241 23).mpr (hmod.of_dvd hd)
  have hperiod : (3 : ZMod 23) ^ 11 = 1 := by decide
  have hpow : ((3 : ZMod 23) ^ n) ^ 11 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 11, pow_mul, hperiod, one_pow]
  rw [hres] at hpow
  exact (by decide : (2241 : ZMod 23) ^ 11 ≠ 1) hpow

/-- No prime strictly between 7 and 47 can divide an index satisfying both conditions. -/
theorem modEq_2241_small_prime_not_dvd {n p : ℕ}
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hp : p.Prime) (hlo : 7 < p) (hhi : p < 47) : ¬ p ∣ n := by
  have hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨
      p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 41 ∨ p = 43 := by
    interval_cases p <;> norm_num at hp <;> decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 11 (3 ^ 5) 1)
      ((by decide : 5 ∣ 5040).trans h5040) (by decide)
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 13 (3 ^ 3) 1)
      ((by decide : 3 ∣ 5040).trans h5040) (by decide)
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 17 (3 ^ 16) 1)
      ((by decide : 16 ∣ 5040).trans h5040) (by decide)
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 19 (3 ^ 18) 1)
      ((by decide : 18 ∣ 5040).trans h5040) (by decide)
  · exact excluded_twenty_three hmod
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 29 (3 ^ 28) 1)
      ((by decide : 28 ∣ 5040).trans h5040) (by decide)
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 31 (3 ^ 30) 1)
      ((by decide : 30 ∣ 5040).trans h5040) (by decide)
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 37 (3 ^ 18) 1)
      ((by decide : 18 ∣ 5040).trans h5040) (by decide)
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 41 (3 ^ 8) 1)
      ((by decide : 8 ∣ 5040).trans h5040) (by decide)
  · exact modEq_period_not_dvd hmod (by decide : Nat.ModEq 43 (3 ^ 42) 1)
      ((by decide : 42 ∣ 5040).trans h5040) (by decide)

#print axioms modEq_2241_small_prime_not_dvd

end D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion
