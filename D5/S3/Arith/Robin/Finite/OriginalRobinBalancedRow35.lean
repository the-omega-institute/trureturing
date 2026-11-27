/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinBalancedRow35
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Bounded primality and balanced products check the last pinned Robin interval in the kernel. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
import Mathlib.Data.Nat.Prime.Factorial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open scoped BigOperators

namespace KernelProducts

/-- The small constant used in the gcd test is certified once. -/
private def trialFactorial : ℕ :=
  1281887661020304656462227130435622342907982917444274060142725765884732435203629626521252650029080818756907586691048188270136719696845070865254799038453129746019006402078289581073668155660108791279230567801870688398118051953198178867370166304062453568461463946717279795397355595296352599842111299377895109811046011666756711813403132693692946772169774899249760783625578161808028502376953103449588953047915530496629396299030533927647577931640589216414425060791523108454400000000000000000000000000000000000000000000000000000000000000000

set_option maxRecDepth 8192 in
private theorem trialFactorial_eq : trialFactorial = Nat.factorial 266 := by
  decide +kernel

private def boundedPrime (p : ℕ) : Bool :=
  if p ≤ 266 then decide p.Prime else p.gcd trialFactorial == 1

/-- Every composite below 267² has a prime factor at most 266. -/
private theorem boundedPrime_iff {p : ℕ} (hp : p < 267 * 267) :
    boundedPrime p = true ↔ p.Prime := by
  by_cases h : p ≤ 266
  · simp [boundedPrime, h]
  · simp only [boundedPrime, if_neg h, beq_iff_eq, trialFactorial_eq,
      ← Nat.coprime_iff_gcd_eq_one]
    constructor
    · intro hc
      by_contra hnp
      have hsqrt : p.sqrt ≤ 266 := Nat.le_of_lt_succ (Nat.sqrt_lt.mpr hp)
      have hsmall : p.minFac ≤ 266 :=
        (Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) hnp)).trans hsqrt
      have hlarge := (Nat.coprime_factorial_iff (by omega : p ≠ 1)).mp hc
      omega
    · intro hprime
      exact hprime.coprime_factorial_of_lt (by omega)

private def rangeProduct (f : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => rangeProduct f start n * f (start + n)

private theorem rangeProduct_eq_prod (f : ℕ → ℕ) (start n : ℕ) :
    rangeProduct f start n = ∏ i ∈ Finset.range n, f (start + i) := by
  induction n with
  | zero => simp [rangeProduct]
  | succ n ih => rw [rangeProduct, Finset.prod_range_succ, ih]

private theorem rangeProduct_add (f : ℕ → ℕ) (start leftLen rightLen : ℕ) :
    rangeProduct f start (leftLen + rightLen) =
      rangeProduct f start leftLen * rangeProduct f (start + leftLen) rightLen := by
  simp only [rangeProduct_eq_prod, Finset.prod_range_add, Nat.add_assoc]

private theorem primeProduct_eq (cutoff : ℕ) (f : ℕ → ℕ) (hc : cutoff < 267 * 267) :
    (∏ p ∈ Nat.primesLE cutoff, f p) =
      rangeProduct (fun p => if boundedPrime p then f p else 1) 0 (cutoff + 1) := by
  rw [Nat.primesLE_eq_filter_range, Finset.prod_filter, rangeProduct_eq_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' : p < 267 * 267 := by
    have := Finset.mem_range.mp hp
    omega
  by_cases h : p.Prime
  · have hb := (boundedPrime_iff hp').2 h
    simp only [Nat.zero_add, if_pos h, if_pos hb]
  · have hb : ¬ boundedPrime p = true := fun ht => h ((boundedPrime_iff hp').1 ht)
    simp only [Nat.zero_add, if_neg h, if_neg hb]

private def optimizerFactor (r : Row) (p : ℕ) : ℕ :=
  if boundedPrime p then p ^ r.exponent p else 1

private def sigmaFactor (r : Row) (p : ℕ) : ℕ :=
  if boundedPrime p then ∑ j ∈ Finset.range (r.exponent p + 1), p ^ j else 1


/-- The leaves of the product tree have at most 128 factors when fuel suffices. -/
private def balancedProduct (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, start, len => rangeProduct f start len
  | fuel + 1, start, len =>
    if len ≤ 128 then rangeProduct f start len
    else
      let mid := len / 2
      balancedProduct f fuel start mid *
        balancedProduct f fuel (start + mid) (len - mid)

private theorem balancedProduct_eq (f : ℕ → ℕ) (fuel start len : ℕ) :
    balancedProduct f fuel start len = rangeProduct f start len := by
  induction fuel generalizing start len with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : len ≤ 128
    · simp [balancedProduct, h]
    · simp only [balancedProduct, if_neg h, ih]
      have hadd : len / 2 + (len - len / 2) = len := by omega
      calc
        _ = rangeProduct f start (len / 2 + (len - len / 2)) :=
          (rangeProduct_add f start (len / 2) (len - len / 2)).symm
        _ = _ := congrArg (rangeProduct f start) hadd

def rowOptimizer (r : Row) : ℕ :=
  balancedProduct (optimizerFactor r) 10 0 (r.cuts[0]! + 1)

def rowSigma (r : Row) : ℕ :=
  balancedProduct (sigmaFactor r) 10 0 (r.cuts[0]! + 1)

theorem row_optimizer {r : Row} (hc : r.cuts[0]! < 267 * 267) :
    r.optimizer = rowOptimizer r := by
  unfold Row.optimizer rowOptimizer
  rw [balancedProduct_eq]
  exact primeProduct_eq _ _ hc

theorem row_sigma {r : Row} (hc : r.cuts[0]! < 267 * 267) :
    r.sigmaProduct = rowSigma r := by
  unfold Row.sigmaProduct rowSigma
  rw [balancedProduct_eq]
  exact primeProduct_eq _ _ hc

theorem gain_of_nat {sigma optimizer num den : ℕ} (hden : 0 < den)
    (h : sigma * den ≤ num * optimizer) :
    (sigma : ℚ) ≤ ((num : ℚ) / (den : ℚ)) * (optimizer : ℚ) := by
  have hden' : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
  rw [div_mul_eq_mul_div₀, le_div_iff₀ hden']
  exact_mod_cast h

theorem height_of_nat {optimizer num den exponent : ℕ} (hden : 0 < den)
    (h : (2 : ℕ) ^ exponent * num ≤ optimizer * den) :
    (2 : ℚ) ^ exponent * ((num : ℚ) / (den : ℚ)) ≤ (optimizer : ℚ) := by
  have hden' : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
  rw [← mul_div_assoc, div_le_iff₀ hden']
  exact_mod_cast h

end KernelProducts

open KernelProducts

def pinnedRow35 : Row where
  lo := (33566442549 / 500000)
  hi := (37283397387 / 500000)
  price := (157973183 / 125000000000000)
  gainUpper := (19886145984323 / 1000000000000)
  heightMantissa := (33702234942557961101 / 18446744073709551616)
  logLoLower := (2778607323 / 250000000)
  logHiLower := (448778023 / 40000000)
  heightExponent := 102220
  cuts := [70849, 365, 57, 22, 12, 8, 6, 5, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2]

section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem row35Cutoff : pinnedRow35.cuts[0]! < 267 * 267 := by
  decide +kernel

private theorem row35Optimizer : pinnedRow35.optimizer = rowOptimizer pinnedRow35 :=
  row_optimizer row35Cutoff

private theorem row35Sigma : pinnedRow35.sigmaProduct = rowSigma pinnedRow35 :=
  row_sigma row35Cutoff

set_option maxHeartbeats 40000000 in
private theorem row35GainNat :
    (rowSigma pinnedRow35) * 1000000000000 ≤ 19886145984323 * (rowOptimizer pinnedRow35) := by
  decide +kernel

-- Keep the exponents in the arithmetic decision at or below 255.
set_option maxHeartbeats 40000000 in
private theorem row35HeightNat :
    ((((2 : ℕ) ^ 200) ^ 255) ^ 2 * 2 ^ 220) * 33702234942557961101 ≤
      (rowOptimizer pinnedRow35) * 18446744073709551616 := by
  decide +kernel

private theorem row35Power :
    (2 : ℕ) ^ 102220 = (((2 : ℕ) ^ 200) ^ 255) ^ 2 * 2 ^ 220 := by
  calc
    (2 : ℕ) ^ 102220 = (2 : ℕ) ^ (200 * 255 * 2 + 220) :=
      congrArg (fun k : ℕ => (2 : ℕ) ^ k) (by decide)
    _ = _ := by simp only [pow_add, pow_mul]

private theorem row35Gain :
    (pinnedRow35.sigmaProduct : ℚ) ≤ pinnedRow35.gainUpper * (pinnedRow35.optimizer : ℚ) := by
  rw [row35Sigma, row35Optimizer]
  change ((rowSigma pinnedRow35) : ℚ) ≤
    (19886145984323 / 1000000000000 : ℚ) * ((rowOptimizer pinnedRow35) : ℚ)
  exact gain_of_nat (by decide : (0 : ℕ) < 1000000000000) row35GainNat

private theorem row35Height :
    (2 : ℚ) ^ pinnedRow35.heightExponent * pinnedRow35.heightMantissa ≤
      (pinnedRow35.optimizer : ℚ) := by
  rw [row35Optimizer]
  change (2 : ℚ) ^ 102220 * (33702234942557961101 / 18446744073709551616 : ℚ) ≤
    ((rowOptimizer pinnedRow35) : ℚ)
  apply height_of_nat (optimizer := (rowOptimizer pinnedRow35)) (num := 33702234942557961101)
    (exponent := 102220) (by decide : (0 : ℕ) < 18446744073709551616)
  rw [row35Power]
  exact row35HeightNat

end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem pinnedRow35_checks : Checks pinnedRow35 where
  price_pos := by decide +kernel
  interval := by decide +kernel
  descending := by decide +kernel
  top := by decide +kernel
  next := by decide +kernel
  stop := by decide +kernel
  gain_normalized := by decide +kernel
  height_normalized := by decide +kernel
  gain := row35Gain
  height := row35Height
  left := by decide +kernel
  right := by decide +kernel

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
