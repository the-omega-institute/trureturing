/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinFiniteRows
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Finite/OriginalRobinFiniteRows
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Native Robin inequality through the pinned Row 04 endpoint. -/

import D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows

/-!
The prices, cuts and interval data come from Jonas Whidden's Robin1984,
pinned at 5ce18bf3487c68d9353276ef5811057f60d17808.
https://github.com/kimihiro64/Robin1984/blob/5ce18bf3487c68d9353276ef5811057f60d17808/Robin1984/Finite/Certificates/Row02.lean
https://github.com/kimihiro64/Robin1984/blob/5ce18bf3487c68d9353276ef5811057f60d17808/Robin1984/Finite/Certificates/Row04.lean

The native atanh series bounds the logarithms. For each row the prime
roster reconstructs the optimizer and the divisor sum. The endpoint
calculations weaken the stored bounds on log of the height by 10⁻⁸ to
use the native lower bound for log 2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

namespace D5.S3.Arith.Robin.Finite.OriginalRobinFiniteRows

open Finset
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows
open D5.S3.Weil.GronwallLowerEnvelope

open private layerRatio from D5.S3.Arith.Robin.Finite.RobinRow01
open private factorization_roster sigma_roster optimal_of_cuts fixed_price_interval
  from D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows

private def mantissa (x : ℝ) (s : ℕ) : ℝ := x / (2 : ℝ) ^ s

private def logLower (x : ℝ) (s : ℕ) : ℝ :=
  s * (6931471803 / 10000000000 : ℝ) + atanhPartial (atanhParameter (mantissa x s)) 10

private def logUpper (x : ℝ) (s : ℕ) : ℝ :=
  let t := atanhParameter (mantissa x s)
  s * (6931471808 / 10000000000 : ℝ) + atanhPartial t 10 +
    2 * t ^ 21 / (21 * (1 - t ^ 2))

private theorem log_bounds {x : ℝ} {s : ℕ}
    (h1 : 1 ≤ mantissa x s) (h2 : mantissa x s < 2) :
    logLower x s ≤ Real.log x ∧ Real.log x ≤ logUpper x s := by
  have hsplit : (2 : ℝ) ^ s * mantissa x s = x := by
    rw [mantissa, mul_comm]
    exact div_mul_cancel₀ x (pow_ne_zero _ two_ne_zero)
  have hm : 0 < mantissa x s := zero_lt_one.trans_le h1
  have hlog : Real.log x = (s : ℝ) * Real.log 2 + Real.log (mantissa x s) := by
    calc
      _ = Real.log ((2 : ℝ) ^ s * mantissa x s) := congrArg Real.log hsplit.symm
      _ = _ := by rw [Real.log_mul (by positivity) hm.ne', Real.log_pow]
  have hl := mul_le_mul_of_nonneg_left log_two_decimal_bounds.1.le
    (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hu := mul_le_mul_of_nonneg_left log_two_decimal_bounds.2.le
    (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have h := log_expansion_remainder_bound h1 h2 10
  norm_num [logRemainder] at h
  unfold logLower logUpper
  constructor
  · linarith only [hlog, hl, h.1]
  · linarith only [hlog, hu, h.2]

private theorem cut_above {q : ℝ} {p k : ℕ} (s : ℕ) (hq : 0 < q) (hp : 1 < p)
    (hp1 : 1 ≤ mantissa p s) (hp2 : mantissa p s < 2)
    (hr1 : 1 ≤ mantissa (layerRatio p k) 0) (hr2 : mantissa (layerRatio p k) 0 < 2)
    (hcalc : q * logUpper p s < logLower (layerRatio p k) 0) :
    q < goldenLayerMarginal p k := by
  have hpLog := (log_bounds hp1 hp2).2
  have hrLog := (log_bounds hr1 hr2).1
  change q < Real.log (layerRatio p k) / Real.log (p : ℝ)
  rw [lt_div_iff₀ (Real.log_pos (by exact_mod_cast hp))]
  exact ((mul_le_mul_of_nonneg_left hpLog hq.le).trans_lt hcalc).trans_le hrLog

private theorem cut_below {q : ℝ} {p k : ℕ} (s : ℕ) (hq : 0 < q) (hp : 1 < p)
    (hp1 : 1 ≤ mantissa p s) (hp2 : mantissa p s < 2)
    (hr1 : 1 ≤ mantissa (layerRatio p k) 0) (hr2 : mantissa (layerRatio p k) 0 < 2)
    (hcalc : logUpper (layerRatio p k) 0 < q * logLower p s) :
    goldenLayerMarginal p k < q := by
  have hpLog := (log_bounds hp1 hp2).1
  have hrLog := (log_bounds hr1 hr2).2
  change Real.log (layerRatio p k) / Real.log (p : ℝ) < q
  rw [div_lt_iff₀ (Real.log_pos (by exact_mod_cast hp))]
  exact (hrLog.trans_lt hcalc).trans_le (mul_le_mul_of_nonneg_left hpLog hq.le)

private theorem cut_pair {q : ℝ} {p k : ℕ} (s t : ℕ) (hq : 0 < q) (hp : 1 < p)
    (hp1 : 1 ≤ mantissa p s) (hp2 : mantissa p s < 2)
    (hn1 : 1 ≤ mantissa (↑(p + 1 : ℕ) : ℝ) t)
    (hn2 : mantissa (↑(p + 1 : ℕ) : ℝ) t < 2)
    (hr1 : 1 ≤ mantissa (layerRatio p k) 0) (hr2 : mantissa (layerRatio p k) 0 < 2)
    (hs1 : 1 ≤ mantissa (layerRatio (p + 1) k) 0)
    (hs2 : mantissa (layerRatio (p + 1) k) 0 < 2)
    (ha : q * logUpper p s < logLower (layerRatio p k) 0)
    (hb : logUpper (layerRatio (p + 1) k) 0 < q * logLower (↑(p + 1 : ℕ) : ℝ) t) :
    q < goldenLayerMarginal p k ∧ goldenLayerMarginal (p + 1) k < q :=
  ⟨cut_above s hq hp hp1 hp2 hr1 hr2 ha, cut_below t hq (by omega) hn1 hn2 hs1 hs2 hb⟩

private theorem row_factorization {S : Finset ℕ} {m cap : ℕ} {e : ℕ → ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hcap : S = Nat.primesLE cap)
    (hprod : m = ∏ p ∈ S, p ^ e p) (hout : ∀ p, cap < p → e p = 0)
    {p : ℕ} (hp : p.Prime) : m.factorization p = e p := by
  rw [hprod, factorization_roster _ hS, hcap]
  by_cases h : p ≤ cap
  · rw [if_pos (Nat.mem_primesLE.mpr ⟨h, hp⟩)]
  · rw [if_neg (fun hm => h (Nat.mem_primesLE.mp hm).1), hout p (lt_of_not_ge h)]

private def objectiveUpper (q gain heightMantissa : ℝ) (e s : ℕ) : ℝ :=
  logUpper gain s - q * (e * (6931471803 / 10000000000 : ℝ) + logLower heightMantissa 0)

private theorem objective_le {q gain heightMantissa : ℝ} {m e s : ℕ}
    (hq : 0 < q) (hm : 1 ≤ m)
    (hg1 : 1 ≤ mantissa gain s) (hg2 : mantissa gain s < 2)
    (ht1 : 1 ≤ mantissa heightMantissa 0) (ht2 : mantissa heightMantissa 0 < 2)
    (hgain : (ArithmeticFunction.sigma 1 m : ℝ) / m ≤ gain)
    (hheight : (2 : ℝ) ^ e * heightMantissa ≤ m) :
    goldenResourceObjective q m ≤ objectiveUpper q gain heightMantissa e s := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hs0 : (0 : ℝ) < (ArithmeticFunction.sigma 1 m : ℝ) :=
    Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 m (by omega))
  have ht0 : 0 < heightMantissa := by
    norm_num [mantissa] at ht1
    linarith
  have hg := (Real.log_le_log (div_pos hs0 hm0) hgain).trans (log_bounds hg1 hg2).2
  have ht := Real.log_le_log (mul_pos (pow_pos (by norm_num) e) ht0) hheight
  rw [Real.log_mul (by positivity) ht0.ne', Real.log_pow] at ht
  have htwo := mul_le_mul_of_nonneg_left log_two_decimal_bounds.1.le
    (Nat.cast_nonneg e : (0 : ℝ) ≤ e)
  have hh := (add_le_add htwo (log_bounds ht1 ht2).1).trans ht
  have hpay := mul_le_mul_of_nonneg_left hh hq.le
  rw [golden_resource_sigma_identity q hm]
  unfold objectiveUpper
  linarith only [hg, hpay]

private theorem endpoint_gap {q H ell upper : ℝ} {m s t : ℕ}
    (hobj : goldenResourceObjective q m ≤ upper)
    (hH1 : 1 ≤ mantissa H s) (hH2 : mantissa H s < 2)
    (hE1 : 1 ≤ mantissa ell t) (hE2 : mantissa ell t < 2)
    (hE0 : 0 < ell) (hEll : ell ≤ logLower H s)
    (hcalc : upper < (5772155 / 10000000 : ℝ) + logLower ell t - q * H) :
    0 < robinThreshold H - q * H - goldenResourceObjective q m := by
  have hlog := Real.log_le_log hE0 (hEll.trans (log_bounds hH1 hH2).1)
  have hloglog := (log_bounds hE1 hE2).1.trans hlog
  unfold robinThreshold
  linarith only [hobj, hloglog, hcalc, eulerMascheroni_decimal_bounds.1]

def originalRow02Price : ℝ := 5519615043151 / 1000000000000000

def originalRow02Integer : ℕ := 791245405339403414400

private def row02Cut (k : ℕ) : ℕ :=
  if k = 1 then 46 else if k = 2 then 8 else if k = 3 then 4 else if k = 4 then 3 else 2

private def row02Exponent (p : ℕ) : ℕ :=
  if p ≤ 2 then 7 else if p ≤ 3 then 4 else if p ≤ 4 then 3 else
  if p ≤ 8 then 2 else if p ≤ 46 then 1 else 0

private def row02Primes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

private theorem row02_price_pos : 0 < originalRow02Price := by norm_num [originalRow02Price]
private theorem row02_primes : ∀ p ∈ row02Primes, p.Prime := by decide
private theorem row02_primes_eq : row02Primes = Nat.primesLE 46 := by decide

private theorem row02_product :
    originalRow02Integer = ∏ p ∈ row02Primes, p ^ row02Exponent p := by
  norm_num [originalRow02Integer, row02Primes, row02Exponent, Finset.prod_insert]

private theorem row02_factorization (p : ℕ) (hp : p.Prime) :
    originalRow02Integer.factorization p = row02Exponent p := by
  refine row_factorization row02_primes row02_primes_eq row02_product ?_ hp
  intro r hr
  unfold row02Exponent
  split_ifs <;> omega

private theorem row02_member (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hK : k ≤ 7) :
    p ≤ row02Cut k ↔ k ≤ originalRow02Integer.factorization p := by
  rw [row02_factorization p hp]
  interval_cases k <;> simp [row02Cut, row02Exponent] <;> split_ifs <;> omega

private theorem row02_signs (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 7) :
    originalRow02Price < goldenLayerMarginal (row02Cut k) k ∧
      goldenLayerMarginal (row02Cut k + 1) k < originalRow02Price := by
  interval_cases k
  · apply cut_pair 5 5 row02_price_pos <;>
      norm_num [row02Cut, originalRow02Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 3 3 row02_price_pos <;>
      norm_num [row02Cut, originalRow02Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 2 2 row02_price_pos <;>
      norm_num [row02Cut, originalRow02Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 2 row02_price_pos <;>
      norm_num [row02Cut, originalRow02Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 1 row02_price_pos <;>
      norm_num [row02Cut, originalRow02Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 1 row02_price_pos <;>
      norm_num [row02Cut, originalRow02Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 1 row02_price_pos <;>
      norm_num [row02Cut, originalRow02Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]

private theorem row02_stop : goldenLayerMarginal 2 8 < originalRow02Price := by
  apply cut_below 1 row02_price_pos <;>
    norm_num [originalRow02Price, logLower, logUpper, mantissa, layerRatio,
      atanhPartial, atanhParameter, Finset.sum_range_succ]

theorem original_row02_optimal : IsGoldenResourceOptimal originalRow02Price originalRow02Integer := by
  apply optimal_of_cuts row02_price_pos (by norm_num [originalRow02Integer]) 7 row02Cut
  · intro k hk hK
    interval_cases k <;> norm_num [row02Cut]
  · exact row02_signs
  · exact row02_stop
  · intro p hp
    rw [row02_factorization p hp]
    unfold row02Exponent
    split_ifs <;> omega
  · exact row02_member

private theorem row02_sigma : ArithmeticFunction.sigma 1 originalRow02Integer =
    5335092099099721728000 := by
  rw [row02_product, sigma_roster _ row02_primes]
  norm_num [row02Primes, row02Exponent, Finset.prod_insert, Finset.sum_range_succ]

private theorem row02_objective :
    goldenResourceObjective originalRow02Price originalRow02Integer ≤
      objectiveUpper originalRow02Price (3371325800503 / 500000000000)
        (6181604729214089175 / 4611686018427387904) 69 2 := by
  apply objective_le row02_price_pos (by norm_num [originalRow02Integer])
  · norm_num [mantissa]
  · norm_num [mantissa]
  · norm_num [mantissa]
  · norm_num [mantissa]
  · rw [row02_sigma]
    norm_num [originalRow02Integer]
  · norm_num [originalRow02Integer]

theorem original_row02_margin {n : ℕ} (hn : 1 ≤ n)
    (hL : 35788699 / 1000000 ≤ Real.log (n : ℝ))
    (hU : Real.log (n : ℝ) ≤ 29149999 / 500000) :
    0 < robinLogMargin n := by
  apply fixed_price_interval (by norm_num [originalRow02Integer]) hn original_row02_optimal
    (by norm_num) (by norm_num) hL hU
  · apply endpoint_gap (s := 5) (t := 1)
        (ell := 894408043 / 250000000 - 1 / 100000000) row02_objective <;>
      norm_num [originalRow02Price, objectiveUpper, logLower, logUpper, mantissa,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply endpoint_gap (s := 5) (t := 2)
        (ell := 2032801029 / 500000000 - 1 / 100000000) row02_objective <;>
      norm_num [originalRow02Price, objectiveUpper, logLower, logUpper, mantissa,
        atanhPartial, atanhParameter, Finset.sum_range_succ]

def originalRow04Price : ℝ := 1724212981141 / 1000000000000000

def originalRow04Integer : ℕ := 8201519488959040182625924708238885435575055666675808000

private def row04Cut (k : ℕ) : ℕ :=
  if k = 1 then 120 else if k = 2 then 14 else if k = 3 then 6 else
  if k = 4 then 4 else if k = 5 then 3 else 2

private def row04Exponent (p : ℕ) : ℕ :=
  if p ≤ 2 then 8 else if p ≤ 3 then 5 else if p ≤ 4 then 4 else
  if p ≤ 6 then 3 else if p ≤ 14 then 2 else if p ≤ 120 then 1 else 0

private def row04Primes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113}

private theorem row04_price_pos : 0 < originalRow04Price := by norm_num [originalRow04Price]
private theorem row04_primes : ∀ p ∈ row04Primes, p.Prime := by decide
private theorem row04_primes_eq : row04Primes = Nat.primesLE 120 := by decide

private theorem row04_product :
    originalRow04Integer = ∏ p ∈ row04Primes, p ^ row04Exponent p := by
  norm_num [originalRow04Integer, row04Primes, row04Exponent, Finset.prod_insert]

private theorem row04_factorization (p : ℕ) (hp : p.Prime) :
    originalRow04Integer.factorization p = row04Exponent p := by
  refine row_factorization row04_primes row04_primes_eq row04_product ?_ hp
  intro r hr
  unfold row04Exponent
  split_ifs <;> omega

private theorem row04_member (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hK : k ≤ 8) :
    p ≤ row04Cut k ↔ k ≤ originalRow04Integer.factorization p := by
  rw [row04_factorization p hp]
  interval_cases k <;> simp [row04Cut, row04Exponent] <;> split_ifs <;> omega

private theorem row04_signs (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 8) :
    originalRow04Price < goldenLayerMarginal (row04Cut k) k ∧
      goldenLayerMarginal (row04Cut k + 1) k < originalRow04Price := by
  interval_cases k
  · apply cut_pair 6 6 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 3 3 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 2 2 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 2 2 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 2 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 1 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 1 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply cut_pair 1 1 row04_price_pos <;>
      norm_num [row04Cut, originalRow04Price, logLower, logUpper, mantissa, layerRatio,
        atanhPartial, atanhParameter, Finset.sum_range_succ]

private theorem row04_stop : goldenLayerMarginal 2 9 < originalRow04Price := by
  apply cut_below 1 row04_price_pos <;>
    norm_num [originalRow04Price, logLower, logUpper, mantissa, layerRatio,
      atanhPartial, atanhParameter, Finset.sum_range_succ]

theorem original_row04_optimal : IsGoldenResourceOptimal originalRow04Price originalRow04Integer := by
  apply optimal_of_cuts row04_price_pos (by norm_num [originalRow04Integer]) 8 row04Cut
  · intro k hk hK
    interval_cases k <;> norm_num [row04Cut]
  · exact row04_signs
  · exact row04_stop
  · intro p hp
    rw [row04_factorization p hp]
    unfold row04Exponent
    split_ifs <;> omega
  · exact row04_member

private theorem row04_sigma : ArithmeticFunction.sigma 1 originalRow04Integer =
    69749120331538766217035847570253344442608462594048000000 := by
  rw [row04_product, sigma_roster _ row04_primes]
  norm_num [row04Primes, row04Exponent, Finset.prod_insert, Finset.sum_range_succ]

private theorem row04_objective :
    goldenResourceObjective originalRow04Price originalRow04Integer ≤
      objectiveUpper originalRow04Price (1700882877263 / 200000000000)
        (24680549958221430113 / 18446744073709551616) 182 3 := by
  apply objective_le row04_price_pos (by norm_num [originalRow04Integer])
  · norm_num [mantissa]
  · norm_num [mantissa]
  · norm_num [mantissa]
  · norm_num [mantissa]
  · rw [row04_sigma]
    norm_num [originalRow04Integer]
  · norm_num [originalRow04Integer]

theorem original_row04_margin {n : ℕ} (hn : 1 ≤ n)
    (hL : 47544747 / 500000 ≤ Real.log (n : ℝ))
    (hU : Real.log (n : ℝ) ≤ 146801491 / 1000000) :
    0 < robinLogMargin n := by
  apply fixed_price_interval (by norm_num [originalRow04Integer]) hn original_row04_optimal
    (by norm_num) (by norm_num) hL hU
  · apply endpoint_gap (s := 6) (t := 2)
        (ell := 4554818489 / 1000000000 - 1 / 100000000) row04_objective <;>
      norm_num [originalRow04Price, objectiveUpper, logLower, logUpper, mantissa,
        atanhPartial, atanhParameter, Finset.sum_range_succ]
  · apply endpoint_gap (s := 7) (t := 2)
        (ell := 4989081271 / 1000000000 - 1 / 100000000) row04_objective <;>
      norm_num [originalRow04Price, objectiveUpper, logLower, logUpper, mantissa,
        atanhPartial, atanhParameter, Finset.sum_range_succ]

/-- Pinned Row 04 overlaps the existing native height-101 certificate. -/
theorem robin_margin_through_pinned_row04 {n : ℕ} (hn : 5040 < n)
    (hU : Real.log (n : ℝ) ≤ 146801491 / 1000000) : 0 < robinLogMargin n := by
  by_cases h101 : Real.log (n : ℝ) ≤ 101
  · exact robin_margin_through_height_101 hn h101
  · have hLo : (47544747 / 500000 : ℝ) ≤ 101 := by norm_num
    exact original_row04_margin (by omega) (hLo.trans (lt_of_not_ge h101).le) hU

theorem original_robin_through_pinned_row04 {n : ℕ} (hn : 5040 < n)
    (hU : Real.log (n : ℝ) ≤ 146801491 / 1000000) :
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) :=
  original_robin_of_margin (by omega) (robin_margin_through_pinned_row04 hn hU)

end D5.S3.Arith.Robin.Finite.OriginalRobinFiniteRows
