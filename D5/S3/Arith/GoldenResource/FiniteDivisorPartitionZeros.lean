/- GID: D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite divisor partition functions have explicit local zeros and no zeros off the imaginary axis. -/

import D5.S3.Weil.EulerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.GoldenResource.FiniteDivisorPartitionZeros

open scoped BigOperators
open D5.S3.Weil.EulerProduct

/-- The geometric factor with exponents from zero through `a`. -/
def localFactor (p a : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (a + 1), ((p : ℂ) ^ (-s)) ^ i

/-- The finite product over the prime factors of a positive integer. -/
def partition (N : ℕ+) (s : ℂ) : ℂ :=
  ∏ p ∈ N.val.primeFactors, localFactor p (N.val.factorization p) s

private theorem geometric_zero_iff (q : ℂ) (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), q ^ i) = 0 ↔ q ^ (a + 1) = 1 ∧ q ≠ 1 := by
  by_cases hq : q = 1
  · simp [hq]
    exact_mod_cast Nat.succ_ne_zero a
  · rw [geom_sum_eq hq]
    simp [div_eq_zero_iff, sub_eq_zero, hq]

private theorem power_one_iff {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (p : ℂ) ^ (-s) = 1 ↔
      ∃ k : ℤ, s = (k : ℂ) * (2 * Real.pi * Complex.I) / (Real.log p : ℂ) := by
  have h := finite_euler_denominator_eq_zero_iff hp s
  unfold finiteEulerDenominator at h
  rw [sub_eq_zero] at h
  exact eq_comm.trans h

private theorem power_length_one_iff {p : ℕ} (hp : p.Prime) (a : ℕ) (s : ℂ) :
    ((p : ℂ) ^ (-s)) ^ (a + 1) = 1 ↔
      ∃ k : ℤ, s = (k : ℂ) * (2 * Real.pi * Complex.I) /
        ((a + 1 : ℂ) * (Real.log p : ℂ)) := by
  have hn : (a + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
  have hl : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [← Complex.cpow_nat_mul]
  have he : ((a + 1 : ℕ) : ℂ) * -s = -((a + 1 : ℂ) * s) := by push_cast; ring
  rw [he, power_one_iff hp]
  apply exists_congr
  intro k
  rw [eq_div_iff hl, eq_div_iff (mul_ne_zero hn hl)]
  constructor <;> intro h <;> linear_combination h

/-- A local factor vanishes exactly at the nontrivial points of its imaginary lattice.
The exponent `a = 0` is included: both sides are then false. -/
theorem local_factor_eq_zero_iff {p : ℕ} (hp : p.Prime) (a : ℕ) (s : ℂ) :
    localFactor p a s = 0 ↔
      ∃ k : ℤ, s = (k : ℂ) * (2 * Real.pi * Complex.I) /
        ((a + 1 : ℂ) * (Real.log p : ℂ)) ∧ ¬ ((a + 1 : ℕ) : ℤ) ∣ k := by
  have hn : (a + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
  have hl : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  rw [localFactor, geometric_zero_iff, power_length_one_iff hp]
  constructor
  · rintro ⟨⟨k, hk⟩, hq⟩
    refine ⟨k, hk, ?_⟩
    rintro ⟨m, hm⟩
    apply hq
    apply (power_one_iff hp s).mpr
    refine ⟨m, ?_⟩
    rw [hk, hm]
    push_cast
    field_simp
  · rintro ⟨k, hk, hdiv⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    intro hq
    obtain ⟨m, hm⟩ := (power_one_iff hp s).mp hq
    apply hdiv
    refine ⟨m, ?_⟩
    have he := hk.symm.trans hm
    have he' : (k : ℂ) = (a + 1 : ℂ) * (m : ℂ) := by
      field_simp at he
      exact he
    exact_mod_cast he'

/-- The modulus of a local geometric root forces the real part to vanish. -/
theorem local_factor_zero_re {p : ℕ} (hp : p.Prime) (a : ℕ) {s : ℂ}
    (hs : localFactor p a s = 0) : s.re = 0 := by
  have hpow := ((geometric_zero_iff _ a).mp hs).1
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero a)).mp
    simpa only [norm_pow, norm_one] using congrArg norm hpow
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re] at hnorm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := ne_of_gt (by exact_mod_cast hp.one_lt)
  have he : -s.re = 0 := (Real.rpow_right_inj hp0 hp1).mp
    (by simpa only [Real.rpow_zero] using hnorm)
  exact neg_eq_zero.mp he

/-- A finite divisor partition function is nonzero whenever the real part is nonzero. -/
theorem partition_ne_zero_of_re_ne_zero (N : ℕ+) {s : ℂ} (hs : s.re ≠ 0) :
    partition N s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp hz
  exact hs (local_factor_zero_re (Nat.prime_of_mem_primeFactors hp) _ hz)

/-- Every zero of the finite divisor partition function lies on the imaginary axis. -/
theorem partition_zero_re (N : ℕ+) {s : ℂ} (hs : partition N s = 0) : s.re = 0 := by
  by_contra hn
  exact partition_ne_zero_of_re_ne_zero N hn hs

example (p : ℕ) (s : ℂ) : localFactor p 0 s = 1 := by simp [localFactor]
example (s : ℂ) : partition 1 s = 1 := by simp [partition]

#print axioms local_factor_eq_zero_iff
#print axioms local_factor_zero_re
#print axioms partition_ne_zero_of_re_ne_zero
#print axioms partition_zero_re

end D5.S3.Arith.GoldenResource.FiniteDivisorPartitionZeros
