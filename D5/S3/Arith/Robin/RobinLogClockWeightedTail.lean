/- GID: D5/S3/Arith/Robin/RobinLogClockWeightedTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/RobinLogClockWeightedTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Strict Robin logarithmic margin above the weighted tail at the integer log clock. -/

import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import D5.S3.Weil.GronwallLowerEnvelope

/-! At the logarithm of any integer above 5040, the full weighted Chebyshev
 tail is strictly below the logarithmic Robin margin. The divisor Mangoldt
 budget accounts for every prime power, with its own multiplicity, and the
 cutoff includes the equality endpoint. -/

set_option autoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.RobinLogClockWeightedTail

open Finset
open scoped BigOperators
open ArithmeticFunction (vonMangoldt vonMangoldt_apply vonMangoldt_apply_one
  vonMangoldt_apply_pow vonMangoldt_apply_prime vonMangoldt_nonneg vonMangoldt_sum)
open D5.S3.Arith.Robin.CompleteMertensPeak (complete_mertens_ledger psiErrorKernel)
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail
  (eulerMass tail layerTail log_sigma_div_eq_eulerMass_sub_tail)
open D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
  (shiftedTail shifted_tail_bound)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)

/-- The strictly positive gap between the logarithmic Euler factor at a
positive valuation and the corresponding finite Mangoldt prefix. -/
private theorem local_log_lt_prefix {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 1 / 2)
    {m : ℕ} (hm : 1 ≤ m) :
    -Real.log (1 - q) + Real.log (1 - q ^ (m + 1)) <
      ∑ r ∈ range m, q ^ (r + 1) / (r + 1 : ℕ) := by
  have hq1 : q < 1 := by linarith
  let f : ℕ → ℝ := fun r => q ^ (r + 1) / (r + 1 : ℕ)
  have hs : HasSum f (-Real.log (1 - q)) := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using
      (Real.hasSum_pow_div_log_of_abs_lt_one (x := q)
        (by rwa [abs_of_pos hq0]))
  have hsplit := hs.summable.sum_add_tsum_nat_add m
  rw [hs.tsum_eq] at hsplit
  have hprefix : (∑ r ∈ range m, f r) + shiftedTail q m =
      -Real.log (1 - q) := by
    simpa only [f, shiftedTail, Nat.add_assoc] using hsplit
  have hden : 0 < 1 - q := by linarith
  have hm2 : (2 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast (show 2 ≤ m + 1 by omega)
  have hcap : 1 ≤ ((m + 1 : ℕ) : ℝ) * (1 - q) := by
    calc
      1 ≤ 2 * (1 - q) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hm2 hden.le
  have ht : shiftedTail q m < q ^ (m + 1) := by
    refine (shifted_tail_bound hq0 hq1 m).2.trans_le ?_
    rw [div_div]
    exact (div_le_iff₀ (mul_pos (by positivity) hden)).2
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hcap (pow_nonneg hq0.le (m + 1)))
  have hpw : q ^ (m + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hl := Real.log_le_sub_one_of_pos (sub_pos.mpr hpw)
  change -Real.log (1 - q) + Real.log (1 - q ^ (m + 1)) < ∑ r ∈ range m, f r
  linarith only [hprefix, ht, hl]

private def mangoldtWeight (d : ℕ) : ℝ := vonMangoldt d / ((d : ℝ) * Real.log d)

private def divisorMass (n : ℕ) : ℝ := ∑ d ∈ n.divisors, mangoldtWeight d

private def logAbundancy (n : ℕ) : ℝ :=
  Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)

private theorem mangoldtWeight_one : mangoldtWeight 1 = 0 := by
  simp [mangoldtWeight]

private theorem mangoldtWeight_prime_pow {p : ℕ} (hp : p.Prime) (r : ℕ) :
    mangoldtWeight (p ^ (r + 1)) = (p : ℝ)⁻¹ ^ (r + 1) / (r + 1 : ℕ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr0 : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mangoldtWeight, vonMangoldt_apply_pow (Nat.succ_ne_zero r),
    vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow, inv_pow]
  field_simp [hp0, hlp.ne', hr0, pow_ne_zero (r + 1) hp0]

private theorem divisorMass_prime_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    divisorMass (p ^ m) = ∑ r ∈ range m, (p : ℝ)⁻¹ ^ (r + 1) / (r + 1 : ℕ) := by
  unfold divisorMass
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Nat.pow_zero]
  simp only [mangoldtWeight_one, add_zero]
  exact sum_congr rfl (fun r _ => mangoldtWeight_prime_pow hp r)

/-- Off prime powers every summand is zero. For coprime factors the surviving
filtered divisor sets partition the surviving divisors of the product. -/
private theorem divisorMass_mul {a b : ℕ} (hab : a.Coprime b) :
    divisorMass (a * b) = divisorMass a + divisorMass b := by
  classical
  simp only [divisorMass, mangoldtWeight, vonMangoldt_apply, ite_div, zero_div,
    ← Finset.sum_filter]
  rw [Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
    Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hab)]

private theorem logAbundancy_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) : logAbundancy (a * b) = logAbundancy a + logAbundancy b := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr ha).ne'
  have hb0 : (b : ℝ) ≠ 0 := (Nat.cast_pos.mpr hb).ne'
  have hsa : (ArithmeticFunction.sigma 1 a : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 a ha.ne')).ne'
  have hsb : (ArithmeticFunction.sigma 1 b : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 b hb.ne')).ne'
  unfold logAbundancy
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab]
  simp only [Nat.cast_mul, mul_div_mul_comm]
  exact Real.log_mul (div_ne_zero hsa ha0) (div_ne_zero hsb hb0)

/-- Strictness survives multiplication because the coprime recursion has both
factors greater than one. For exponent zero the premise is impossible. -/
private theorem logAbundancy_lt_divisorMass {n : ℕ} (hn : 1 < n) :
    logAbundancy n < divisorMass n := by
  revert hn
  refine Nat.recOnPrimeCoprime
    (motive := fun k => 1 < k → logAbundancy k < divisorMass k) ?_ ?_ ?_ n
  · intro h
    omega
  · intro p m hp hm
    have hm0 : m ≠ 0 := by
      intro hz
      subst m
      simp at hm
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hq0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
    have hq2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    have h := log_sigma_div_eq_eulerMass_sub_tail (N := p ^ m) (pow_pos hp.pos m)
    simp only [eulerMass, tail, Nat.primeFactors_prime_pow hm0 hp, sum_singleton,
      layerTail, Nat.factorization_pow_self hp] at h
    rw [divisorMass_prime_pow hp, logAbundancy, h, sub_neg_eq_add]
    exact local_log_lt_prefix hq0 hq2 (by omega)
  · intro a b ha hb hab ia ib _
    rw [logAbundancy_mul (by omega : 0 < a) (by omega : 0 < b) hab,
      divisorMass_mul hab]
    exact add_lt_add (ia ha) (ib hb)

/-- The signed comparison of two finite selections, with the same linear
weight on both. No sign assumption on the total budget difference is needed. -/
private theorem finite_threshold_budget {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) (w c : ι → ℝ) (rate : ℝ)
    (hlo : ∀ i ∈ B, rate * c i ≤ w i)
    (hhi : ∀ i ∈ A, i ∉ B → w i ≤ rate * c i) :
    (∑ i ∈ A, w i) ≤ (∑ i ∈ B, w i) +
      rate * ((∑ i ∈ A, c i) - (∑ i ∈ B, c i)) := by
  have h : (∑ i ∈ A, (w i - rate * c i)) ≤ ∑ i ∈ B, (w i - rate * c i) := by
    calc
      _ ≤ ∑ i ∈ A ∩ B, (w i - rate * c i) :=
        sum_le_sum_of_subset_of_nonpos inter_subset_left (by
          intro i hi hnot
          exact sub_nonpos.mpr (hhi i hi (by
            simpa only [mem_inter, hi, true_and] using hnot)))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right
        (fun i hi _ => sub_nonneg.mpr (hlo i hi))
  simp only [sum_sub_distrib, ← mul_sum] at h
  rw [mul_sub]
  linarith only [h]

private theorem inv_mul_log_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    1 / (y * Real.log y) ≤ 1 / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ y := hx0.le.trans hxy
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hm : x * Real.log x ≤ y * Real.log y :=
    mul_le_mul hxy (Real.log_le_log hx0 hxy) hlx.le hy0
  exact one_div_le_one_div_of_le (mul_pos hx0 hlx) hm

/-- The exact Mangoldt divisor budget is `log n`; the cutoff budget is `psi y`.
Every selected divisor outside the cutoff has nonpositive signed weight. -/
private theorem divisorMass_le_cutoff (n : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    divisorMass n ≤ (∑ d ∈ Ioc 0 ⌊y⌋₊, mangoldtWeight d) +
      (Real.log (n : ℝ) - Chebyshev.psi y) / (y * Real.log y) := by
  have hy0 : 0 ≤ y := by linarith
  have hy1 : 1 < y := by linarith
  have hw (d : ℕ) : mangoldtWeight d =
      (1 / ((d : ℝ) * Real.log d)) * vonMangoldt d := by
    simp only [mangoldtWeight, div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  have hlo : ∀ d ∈ Ioc 0 ⌊y⌋₊, (1 / (y * Real.log y)) * vonMangoldt d ≤
      mangoldtWeight d := by
    intro d hd
    obtain ⟨hd0, hcut⟩ := Finset.mem_Ioc.mp hd
    by_cases hd1 : d = 1
    · subst d
      simp [mangoldtWeight]
    have hdgt : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    have hdy : (d : ℝ) ≤ y := (Nat.le_floor_iff hy0).mp hcut
    rw [hw]
    exact mul_le_mul_of_nonneg_right (inv_mul_log_antitone hdgt hdy) vonMangoldt_nonneg
  have hhi : ∀ d ∈ n.divisors, d ∉ Ioc 0 ⌊y⌋₊ → mangoldtWeight d ≤
      (1 / (y * Real.log y)) * vonMangoldt d := by
    intro d hd hnot
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hyd : y < (d : ℝ) := by
      by_contra! hdy
      exact hnot (Finset.mem_Ioc.mpr ⟨hd0, Nat.le_floor hdy⟩)
    rw [hw]
    exact mul_le_mul_of_nonneg_right (inv_mul_log_antitone hy1 hyd.le) vonMangoldt_nonneg
  have h := finite_threshold_budget n.divisors (Ioc 0 ⌊y⌋₊) mangoldtWeight
    (fun d => vonMangoldt d) (1 / (y * Real.log y)) hlo hhi
  rw [vonMangoldt_sum] at h
  change divisorMass n ≤ (∑ d ∈ Ioc 0 ⌊y⌋₊, mangoldtWeight d) +
    (1 / (y * Real.log y)) * (Real.log (n : ℝ) - Chebyshev.psi y) at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- The full weighted Mangoldt tail at the actual logarithm of every integer
above 5040 is strictly smaller than its Robin logarithmic margin. -/
theorem weightedTail_lt_robinLogMargin {n : ℕ} (hn : 5040 < n) :
    weightedTail psiErrorKernel (Real.log (n : ℝ)) < robinLogMargin n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn9 : (9 : ℝ) ≤ n := by exact_mod_cast (show 9 ≤ n by omega)
  have hexp : Real.exp 2 < (9 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h₁ := mul_lt_mul_of_pos_right Real.exp_one_lt_three (Real.exp_pos 1)
    have h₂ := mul_lt_mul_of_pos_left Real.exp_one_lt_three (by norm_num : (0 : ℝ) < 3)
    linarith only [h₁, h₂]
  let y : ℝ := Real.log (n : ℝ)
  have hy : 2 ≤ y := ((Real.lt_log_iff_exp_lt hn0).mpr (hexp.trans_le hn9)).le
  have hlocal := logAbundancy_lt_divisorMass (show 1 < n by omega)
  have hbudget := divisorMass_le_cutoff n hy
  change divisorMass n ≤ (∑ d ∈ Ioc 0 ⌊y⌋₊, mangoldtWeight d) +
    (y - Chebyshev.psi y) / (y * Real.log y) at hbudget
  have hledger := (complete_mertens_ledger hy).2.2
  change (∑ d ∈ Ioc 0 ⌊y⌋₊, mangoldtWeight d) - Real.log (Real.log y) - Mertens.γ =
    (Chebyshev.psi y - y) / (y * Real.log y) - weightedTail psiErrorKernel y at hledger
  rw [Mertens.γ.eq_eulerMascheroni] at hledger
  simp only [sub_div] at hbudget hledger
  change weightedTail psiErrorKernel y <
    Real.eulerMascheroniConstant + Real.log (Real.log y) - logAbundancy n
  linarith only [hlocal, hbudget, hledger]

end D5.S3.Arith.Robin.RobinLogClockWeightedTail

#print axioms D5.S3.Arith.Robin.RobinLogClockWeightedTail.weightedTail_lt_robinLogMargin
