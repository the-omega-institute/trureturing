/- GID: D5/S3/Arith/Robin/GronwallAbundant/Local
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/GronwallAbundant/Local
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Local GA1 comparisons constrain every prime-power divisor. -/

import D5.S3.Arith.Robin.PrimeFiberPropagation
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Robin.GronwallAbundant

open Finset Real
open scoped BigOperators ArithmeticFunction.Omega

noncomputable section

/-- The Gronwall quotient with its unmodified natural-logarithm denominator. -/
def gronwallQ (n : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 n : ℝ) / (n * Real.log (Real.log n))

/-- A composite integer whose Gronwall quotient does not increase on deleting a prime. -/
def IsGA1 (N : ℕ) : Prop :=
  ¬ N.Prime ∧ 1 < N ∧ ∀ p ∈ N.primeFactors, gronwallQ (N / p) ≤ gronwallQ N

/-- Proper GA1 integers have at least three prime factors with multiplicity. -/
def IsProperGA1 (N : ℕ) : Prop := IsGA1 N ∧ 3 ≤ N.primeFactorsList.length

/-- The number of proper GA1 integers at most a real cutoff. -/
def Q1 (x : ℝ) : ℕ := by
  classical
  exact ((Finset.range (⌊x⌋₊ + 1)).filter IsProperGA1).card

/-- Deleting a prime from a proper GA1 integer leaves at least two prime factors. -/
theorem proper_div_ge_four {N q : ℕ} (hN : IsProperGA1 N)
    (hq : q ∈ N.primeFactors) : 4 ≤ N / q := by
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd := Nat.dvd_of_mem_primeFactors hq
  have hN0 : N ≠ 0 := by have := hN.1.2.1; omega
  have hm0 : N / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos).ne'
  have hprod : N / q * q = N := Nat.div_mul_cancel hd
  have hc := ArithmeticFunction.cardFactors_mul hm0 hp.ne_zero
  rw [hprod, ArithmeticFunction.cardFactors_apply_prime hp] at hc
  have hh : 2 ≤ ArithmeticFunction.cardFactors (N / q) := by
    change ArithmeticFunction.cardFactors N = _ at hc
    have hlen := hN.2
    change 3 ≤ ArithmeticFunction.cardFactors N at hlen
    omega
  by_contra hn
  have hlt : N / q < 4 := by omega
  interval_cases h : N / q <;> norm_num [h, ArithmeticFunction.cardFactors_apply] at hh

/-- All logarithms in a proper GA1 prime-deletion comparison are positive. -/
theorem proper_loglog_div_pos {N q : ℕ} (hN : IsProperGA1 N)
    (hq : q ∈ N.primeFactors) : 0 < Real.log (Real.log (N / q : ℕ)) := by
  have hm : (3 : ℝ) < (N / q : ℕ) := by exact_mod_cast (show 3 < N / q by have := proper_div_ge_four hN hq; omega)
  have hlog : 1 < Real.log (N / q : ℕ) := by
    have hthree : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact hthree.trans (Real.log_lt_log (by norm_num) hm)
  exact Real.log_pos hlog

/-- The finite geometric sum attached to the complete exponent of a prime. -/
def primeDeletionSum (N q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N.factorization q + 1), (q : ℝ) ^ i

/-- The exact local comparison before changing logarithmic coordinates. -/
theorem ga1_local_criterion {N q : ℕ} (hN : 0 < N)
    (hq : q ∈ N.primeFactors) (hm : 4 ≤ N / q) :
    gronwallQ (N / q) ≤ gronwallQ N ↔
      primeDeletionSum N q *
        (Real.log (Real.log N) - Real.log (Real.log (N / q : ℕ))) ≤
          Real.log (Real.log N) := by
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd := Nat.dvd_of_mem_primeFactors hq
  have hM : 0 < N / q := by omega
  have hprod : N / q * q = N := Nat.div_mul_cancel hd
  have hfac : (N / q).factorization q + 1 = N.factorization q := by
    have hv : 1 ≤ N.factorization q :=
      (hp.dvd_iff_one_le_factorization hN.ne').mp hd
    rw [Nat.factorization_div hd, Finsupp.tsub_apply, hp.factorization]
    simp only [Finsupp.single_eq_same]
    omega
  have hsum : primeDeletionSum N q =
      (q : ℝ) * ArithmeticFunction.sigma 1 (q ^ (N / q).factorization q) + 1 := by
    rw [primeDeletionSum, ← hfac]
    have hs := PrimeFiberPropagation.sigma_prime_pow_succ hp ((N / q).factorization q)
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp] at hs
    exact_mod_cast hs
  have hZ := PrimeFiberPropagation.divisorRatio_pos hM.ne'
  have hZN := PrimeFiberPropagation.divisorRatio_pos hN.ne'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hp.pos
  have hsigma : (0 : ℝ) < ArithmeticFunction.sigma 1 (q ^ (N / q).factorization q) := by
    exact_mod_cast ArithmeticFunction.sigma_pos_iff.mpr (pow_pos hp.pos _)
  have hS : 0 < primeDeletionSum N q - 1 := by rw [hsum]; nlinarith
  have hedge := PrimeFiberPropagation.edge_excess hp hM.ne'
  rw [hprod] at hedge
  have hidentity : PrimeFiberPropagation.divisorRatio N * (primeDeletionSum N q - 1) =
      PrimeFiberPropagation.divisorRatio (N / q) * primeDeletionSum N q := by
    rw [hsum]
    field_simp at hedge ⊢
    nlinarith [hedge]
  have hMR : (3 : ℝ) < (N / q : ℕ) := by exact_mod_cast (show 3 < N / q by omega)
  have hLm : 0 < Real.log (Real.log (N / q : ℕ)) := by
    apply Real.log_pos
    exact (show (1 : ℝ) < Real.log 3 by linarith [Real.log_three_gt_d9]).trans
      (Real.log_lt_log (by norm_num) hMR)
  have hMN : N / q ≤ N := Nat.div_le_self _ _
  have hLN : 0 < Real.log (Real.log N) := lt_of_lt_of_le hLm
    (Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1 < N / q by omega)))
      (Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMN)))
  have hQ (n : ℕ) : gronwallQ n =
      PrimeFiberPropagation.divisorRatio n / Real.log (Real.log n) := by
    simp only [gronwallQ, PrimeFiberPropagation.divisorRatio, div_div]
  rw [hQ, hQ, div_le_div_iff₀ hLm hLN]
  constructor
  · intro h
    have hh := mul_le_mul_of_nonneg_right h hS.le
    have hscaled : PrimeFiberPropagation.divisorRatio (N / q) *
        ((primeDeletionSum N q - 1) * Real.log (Real.log N)) ≤
        PrimeFiberPropagation.divisorRatio (N / q) *
        (primeDeletionSum N q * Real.log (Real.log (N / q : ℕ))) := by
      calc
        _ = (PrimeFiberPropagation.divisorRatio (N / q) * Real.log (Real.log N)) *
            (primeDeletionSum N q - 1) := by ring
        _ ≤ (PrimeFiberPropagation.divisorRatio N * Real.log (Real.log (N / q : ℕ))) *
            (primeDeletionSum N q - 1) := hh
        _ = (PrimeFiberPropagation.divisorRatio N * (primeDeletionSum N q - 1)) *
            Real.log (Real.log (N / q : ℕ)) := by ring
        _ = _ := by rw [hidentity]; ring
    have := (mul_le_mul_iff_right₀ hZ).mp hscaled
    nlinarith
  · intro h
    have hsmall : (primeDeletionSum N q - 1) * Real.log (Real.log N) ≤
        primeDeletionSum N q * Real.log (Real.log (N / q : ℕ)) := by nlinarith
    have hh : PrimeFiberPropagation.divisorRatio (N / q) *
        Real.log (Real.log N) * (primeDeletionSum N q - 1) ≤
        PrimeFiberPropagation.divisorRatio N *
        Real.log (Real.log (N / q : ℕ)) * (primeDeletionSum N q - 1) := by
      calc
        _ = PrimeFiberPropagation.divisorRatio (N / q) *
            ((primeDeletionSum N q - 1) * Real.log (Real.log N)) := by ring
        _ ≤ PrimeFiberPropagation.divisorRatio (N / q) *
            (primeDeletionSum N q * Real.log (Real.log (N / q : ℕ))) :=
          mul_le_mul_of_nonneg_left hsmall hZ.le
        _ = (PrimeFiberPropagation.divisorRatio (N / q) * primeDeletionSum N q) *
            Real.log (Real.log (N / q : ℕ)) := by ring
        _ = _ := by rw [← hidentity]; ring
    exact (mul_le_mul_iff_left₀ hS).mp hh

/-- Concavity of the logarithm charges deletion by at least its relative log-size. -/
theorem prime_deletion_log_gap {N q : ℕ} (hN : 0 < N)
    (hq : q ∈ N.primeFactors) (hm : 4 ≤ N / q) :
    Real.log q / Real.log N ≤
      Real.log (Real.log N) - Real.log (Real.log (N / q : ℕ)) := by
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd := Nat.dvd_of_mem_primeFactors hq
  have hM : 0 < N / q := by omega
  have hMR : (1 : ℝ) < (N / q : ℕ) := by exact_mod_cast (show 1 < N / q by omega)
  have hMN : N / q ≤ N := Nat.div_le_self _ _
  have hNR : (1 : ℝ) < N := hMR.trans_le (by exact_mod_cast hMN)
  have hLM : 0 < Real.log (N / q : ℕ) := Real.log_pos hMR
  have hLN : 0 < Real.log N := Real.log_pos hNR
  have hqR : (0 : ℝ) < q := by exact_mod_cast hp.pos
  have hprod : ((N / q : ℕ) : ℝ) * q = N := by exact_mod_cast Nat.div_mul_cancel hd
  have hlogs : Real.log (N / q : ℕ) + Real.log q = Real.log N := by
    rw [← Real.log_mul (by positivity) hqR.ne', hprod]
  have hc := Real.log_le_sub_one_of_pos (div_pos hLM hLN)
  rw [Real.log_div hLM.ne' hLN.ne'] at hc
  have hh : Real.log (N / q : ℕ) / Real.log N - 1 = -Real.log q / Real.log N := by
    field_simp
    linarith
  rw [hh, neg_div] at hc
  linarith

/-- The GA1 comparison bounds every full local geometric sum. -/
theorem ga1_prime_power_log_bound {N q : ℕ} (hN : IsProperGA1 N)
    (hq : q ∈ N.primeFactors) :
    primeDeletionSum N q * Real.log q ≤ Real.log N * Real.log (Real.log N) := by
  have hNpos : 0 < N := by have := hN.1.2.1; omega
  have hm := proper_div_ge_four hN hq
  have hgap := prime_deletion_log_gap hNpos hq hm
  have hcrit := (ga1_local_criterion hNpos hq hm).mp (hN.1.2.2 q hq)
  have hS : 0 ≤ primeDeletionSum N q := by
    unfold primeDeletionSum
    exact Finset.sum_nonneg (fun _ _ => pow_nonneg (Nat.cast_nonneg q) _)
  have hlog : 0 < Real.log N := by
    have hlogm : 0 < Real.log (N / q : ℕ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N / q by omega))
    have hlogm1 : 1 < Real.log (N / q : ℕ) :=
      (Real.log_pos_iff hlogm.le).mp (proper_loglog_div_pos hN hq)
    exact (zero_lt_one.trans hlogm1).trans_le
      (Real.log_le_log (by exact_mod_cast (show 0 < N / q by omega))
        (by exact_mod_cast Nat.div_le_self N q))
  have hh : primeDeletionSum N q * (Real.log q / Real.log N) ≤ Real.log (Real.log N) :=
    (mul_le_mul_of_nonneg_left hgap hS).trans hcrit
  calc
    _ = (primeDeletionSum N q * (Real.log q / Real.log N)) * Real.log N := by
      field_simp
    _ ≤ Real.log (Real.log N) * Real.log N := mul_le_mul_of_nonneg_right hh hlog.le
    _ = _ := by ring

/-- Every prime-power divisor obeys the GA1 logarithmic barrier. -/
theorem ga1_prime_power_le {N q : ℕ} (hN : IsProperGA1 N)
    (hq : q ∈ N.primeFactors) (r : ℕ) (hr : 1 ≤ r)
    (hv : r ≤ N.factorization q) : (q : ℝ) ^ r ≤ (r : ℝ) * Real.log N := by
  have hp := Nat.prime_of_mem_primeFactors hq
  have hqR : (1 : ℝ) < q := by exact_mod_cast hp.one_lt
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN.1.2.1)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpow : (q : ℝ) ^ r ≤ primeDeletionSum N q := by
    unfold primeDeletionSum
    exact Finset.single_le_sum (fun _ _ => pow_nonneg (by positivity) _)
      (Finset.mem_range.mpr (by omega))
  have hbudget := (mul_le_mul_of_nonneg_right hpow hlogq.le).trans
    (ga1_prime_power_log_bound hN hq)
  by_contra hn
  have hbad : (r : ℝ) * Real.log N < (q : ℝ) ^ r := lt_of_not_ge hn
  have hlogbad := Real.log_lt_log (mul_pos (by positivity) hlogN) hbad
  rw [Real.log_mul (by positivity) hlogN.ne', Real.log_pow] at hlogbad
  have hlogr : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrR
  have hfirst : Real.log N * Real.log (Real.log N) <
      Real.log N * ((r : ℝ) * Real.log q) :=
    mul_lt_mul_of_pos_left (by linarith) hlogN
  have hsecond : ((r : ℝ) * Real.log N) * Real.log q < (q : ℝ) ^ r * Real.log q :=
    mul_lt_mul_of_pos_right hbad hlogq
  nlinarith

/-- Every prime factor is at most the natural logarithm of a proper GA1 integer. -/
theorem prime_le_log {N q : ℕ} (hN : IsProperGA1 N) (hq : q ∈ N.primeFactors) :
    (q : ℝ) ≤ Real.log N := by
  have hp := Nat.prime_of_mem_primeFactors hq
  have hv : 1 ≤ N.factorization q :=
    (hp.dvd_iff_one_le_factorization (by have := hN.1.2.1; omega)).mp
      (Nat.dvd_of_mem_primeFactors hq)
  simpa using ga1_prime_power_le hN hq 1 le_rfl hv

/-- Repeated prime factors lie below the square-root cutoff. -/
theorem square_le_two_log {N q : ℕ} (hN : IsProperGA1 N) (hq : q ∈ N.primeFactors)
    (hv : 2 ≤ N.factorization q) : (q : ℝ) ^ 2 ≤ 2 * Real.log N := by
  simpa using ga1_prime_power_le hN hq 2 (by norm_num) hv

/-- A proper GA1 integer has logarithm strictly greater than two. -/
theorem proper_log_gt_two {N : ℕ} (hN : IsProperGA1 N) : 2 < Real.log N := by
  obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hN.1.2.1
  have hp := Nat.prime_of_mem_primeFactors hq
  have hdiv := proper_div_ge_four hN hq
  have hprod := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hq)
  have hN8 : 8 ≤ N := by
    calc
      8 = 4 * 2 := rfl
      _ ≤ (N / q) * q := Nat.mul_le_mul hdiv hp.two_le
      _ = N := hprod
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 8)
    (show (8 : ℝ) ≤ N by exact_mod_cast hN8)
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog8] at hlog
  linarith [Real.log_two_gt_d9]

/-- The non-strict logarithmic threshold used in common GA1 budgets. -/
theorem proper_log_ge_two {N : ℕ} (hN : IsProperGA1 N) : 2 ≤ Real.log N :=
  (proper_log_gt_two hN).le

end
end D5.S3.Arith.Robin.GronwallAbundant
