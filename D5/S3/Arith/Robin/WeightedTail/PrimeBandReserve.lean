/- GID: D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/WeightedTail/PrimeBandReserve
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Prime-band cardinality reserve for the Robin slack at the integer log clock. -/

import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import D5.S3.Weil.GronwallLowerEnvelope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.NumberTheory.PrimeCounting

/-! A prime-band lower bound for the Robin slack at the integer logarithmic clock. -/

set_option autoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve

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

/-- The finite Mangoldt prefix, indexed by positive prime-power exponents. -/
private def primePrefix (p m : ℕ) : ℝ :=
  ∑ r ∈ range m, (p : ℝ)⁻¹ ^ (r + 1) / (r + 1 : ℕ)

private def localEulerGap (p m : ℕ) : ℝ :=
  primePrefix p m - (-Real.log (1 - (p : ℝ)⁻¹) +
    Real.log (1 - (p : ℝ)⁻¹ ^ (m + 1)))

private theorem localEulerGap_nonneg {p m : ℕ} (hp : p.Prime) :
    0 ≤ localEulerGap p m := by
  by_cases hm : m = 0
  · subst m
    simp [localEulerGap, primePrefix]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hq2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
  exact sub_nonneg.mpr (local_log_lt_prefix hq0 hq2 (by omega : 1 ≤ m)).le

/-- Reuse the checked coprime recursion to obtain an exact prime-indexed sum. -/
private theorem divisorMass_eq_primePrefix (n : ℕ) :
    divisorMass n = ∑ p ∈ n.primeFactors, primePrefix p (n.factorization p) := by
  classical
  refine Nat.recOnPrimeCoprime
    (motive := fun k => divisorMass k = ∑ p ∈ k.primeFactors, primePrefix p (k.factorization p))
    ?_ ?_ ?_ n
  · simp [divisorMass]
  · intro p m hp
    rw [divisorMass_prime_pow hp]
    by_cases hm : m = 0
    · subst m
      simp
    rw [Nat.primeFactors_prime_pow hm hp, sum_singleton, Nat.factorization_pow_self hp]
    rfl
  · intro a b ha hb hab ia ib
    rw [divisorMass_mul hab, ia, ib, hab.primeFactors_mul,
      sum_union hab.disjoint_primeFactors]
    congr 1
    · apply sum_congr rfl
      intro p hp
      have hpb : ¬ p ∣ b := by
        intro hd
        exact (Finset.disjoint_left.mp hab.disjoint_primeFactors hp)
          (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hd, by omega⟩)
      rw [Nat.factorization_mul_apply_of_coprime hab,
        Nat.factorization_eq_zero_of_not_dvd hpb, add_zero]
    · apply sum_congr rfl
      intro p hp
      have hpa : ¬ p ∣ a := by
        intro hd
        exact (Finset.disjoint_left.mp hab.disjoint_primeFactors
          (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hd, by omega⟩)) hp
      rw [Nat.factorization_mul_apply_of_coprime hab,
        Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]

private theorem divisorMass_sub_logAbundancy_eq (n : ℕ) (hn : 0 < n) :
    divisorMass n - logAbundancy n =
      ∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p) := by
  rw [divisorMass_eq_primePrefix, logAbundancy, log_sigma_div_eq_eulerMass_sub_tail hn,
    eulerMass, tail, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  unfold localEulerGap layerTail
  ring

private theorem inv_mul_log_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    1 / (y * Real.log y) ≤ 1 / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ y := hx0.le.trans hxy
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hm : x * Real.log x ≤ y * Real.log y :=
    mul_le_mul hxy (Real.log_le_log hx0 hxy) hlx.le hy0
  exact one_div_le_one_div_of_le (mul_pos hx0 hlx) hm

private def cutoff (y : ℝ) : Finset ℕ := Ioc 0 ⌊y⌋₊
private def rate (y : ℝ) : ℝ := 1 / (y * Real.log y)
private def signedWeight (y : ℝ) (d : ℕ) : ℝ :=
  mangoldtWeight d - rate y * vonMangoldt d

private theorem mangoldtWeight_eq_rate (d : ℕ) :
    mangoldtWeight d = rate (d : ℝ) * vonMangoldt d := by
  unfold mangoldtWeight rate
  ring

private theorem signedWeight_nonneg {y : ℝ} (hy : 2 ≤ y) {d : ℕ}
    (hd : d ∈ cutoff y) : 0 ≤ signedWeight y d := by
  obtain ⟨hd0, hcut⟩ := Finset.mem_Ioc.mp hd
  by_cases hd1 : d = 1
  · subst d
    simp [signedWeight, mangoldtWeight]
  have hdgt : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hdy : (d : ℝ) ≤ y := (Nat.le_floor_iff (by linarith : 0 ≤ y)).mp hcut
  rw [signedWeight, mangoldtWeight_eq_rate]
  exact sub_nonneg.mpr
    (mul_le_mul_of_nonneg_right (inv_mul_log_antitone hdgt hdy) vonMangoldt_nonneg)

private theorem neg_signedWeight_nonneg {n d : ℕ} {y : ℝ} (hy : 2 ≤ y)
    (hd : d ∈ n.divisors) (hnot : d ∉ cutoff y) : 0 ≤ -signedWeight y d := by
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hyd : y < (d : ℝ) := by
    by_contra! hdy
    exact hnot (Finset.mem_Ioc.mpr ⟨hd0, Nat.le_floor hdy⟩)
  rw [signedWeight, mangoldtWeight_eq_rate, neg_sub]
  exact sub_nonneg.mpr
    (mul_le_mul_of_nonneg_right (inv_mul_log_antitone (by linarith : 1 < y) hyd.le)
      vonMangoldt_nonneg)

/-- The cutoff comparison is an equality with two nonnegative mismatch sums.
The common intersection cancels. The Mangoldt costs are exactly log n and psi y. -/
private theorem mismatch_eq (n : ℕ) (y : ℝ) :
    (∑ d ∈ cutoff y \ n.divisors, signedWeight y d) +
      (∑ d ∈ n.divisors \ cutoff y, -signedWeight y d) =
      (∑ d ∈ cutoff y, mangoldtWeight d) - divisorMass n +
        rate y * (Real.log (n : ℝ) - Chebyshev.psi y) := by
  classical
  have hA := Finset.sum_inter_add_sum_sdiff n.divisors (cutoff y) (signedWeight y)
  have hB := Finset.sum_inter_add_sum_sdiff (cutoff y) n.divisors (signedWeight y)
  rw [inter_comm (cutoff y) n.divisors] at hB
  have hcostA : (∑ d ∈ n.divisors, signedWeight y d) =
      divisorMass n - rate y * Real.log (n : ℝ) := by
    simp only [signedWeight, sum_sub_distrib, ← mul_sum, vonMangoldt_sum, divisorMass]
  have hcostB : (∑ d ∈ cutoff y, signedWeight y d) =
      (∑ d ∈ cutoff y, mangoldtWeight d) - rate y * Chebyshev.psi y := by
    simp only [signedWeight, sum_sub_distrib, ← mul_sum, cutoff, Chebyshev.psi]
  rw [hcostA] at hA
  rw [hcostB] at hB
  rw [Finset.sum_neg_distrib, mul_sub]
  linarith only [hA, hB]

/-- Exact transport of the two arithmetic gaps to the weighted analytic tail.
The signed correction (y - psi y)/(y log y) cancels the ledger endpoint. -/
private theorem robin_slack_eq {n : ℕ} (hn : 0 < n)
    (hy : 2 ≤ Real.log (n : ℝ)) :
    robinLogMargin n - weightedTail psiErrorKernel (Real.log (n : ℝ)) =
      (∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p)) +
      (∑ d ∈ cutoff (Real.log (n : ℝ)) \ n.divisors, signedWeight (Real.log (n : ℝ)) d) +
      (∑ d ∈ n.divisors \ cutoff (Real.log (n : ℝ)), -signedWeight (Real.log (n : ℝ)) d) := by
  let y : ℝ := Real.log (n : ℝ)
  have hg := divisorMass_sub_logAbundancy_eq n hn
  have hm := mismatch_eq n y
  change 2 ≤ y at hy
  have hledger := (complete_mertens_ledger hy).2.2
  change (∑ d ∈ cutoff y, mangoldtWeight d) - Real.log (Real.log y) - Mertens.γ =
    (Chebyshev.psi y - y) / (y * Real.log y) - weightedTail psiErrorKernel y at hledger
  rw [Mertens.γ.eq_eulerMascheroni] at hledger
  have hrate : rate y * (Real.log (n : ℝ) - Chebyshev.psi y) =
      -(Chebyshev.psi y - y) / (y * Real.log y) := by
    change (1 / (y * Real.log y)) * (y - Chebyshev.psi y) = _
    ring
  rw [hrate] at hm
  rw [neg_div] at hm
  change Real.eulerMascheroniConstant + Real.log (Real.log y) - logAbundancy n -
    weightedTail psiErrorKernel y =
      (∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p)) +
      (∑ d ∈ cutoff y \ n.divisors, signedWeight y d) +
      (∑ d ∈ n.divisors \ cutoff y, -signedWeight y d)
  linarith only [hg, hm, hledger]

/-- q - log(1+q) ≥ q²/(2(1+q)). For the derivative comparison use
F(t) = t + t²/2 - (1+t) log(1+t), F'(t) = t - log(1+t) ≥ 0. -/
private theorem log_one_add_gap {q : ℝ} (hq : 0 ≤ q) :
    q ^ 2 / (2 * (1 + q)) ≤ q - Real.log (1 + q) := by
  let f : ℝ → ℝ := fun t => t + t ^ 2 / 2 - (1 + t) * Real.log (1 + t)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt f (t - Real.log (1 + t)) t := by
    have hne : (1 : ℝ) + t ≠ 0 := by linarith
    have hid : HasDerivAt (fun z : ℝ => z) 1 t := hasDerivAt_id t
    have hadd : HasDerivAt (fun z : ℝ => 1 + z) 1 t := hid.const_add 1
    have hl : HasDerivAt (fun z : ℝ => Real.log (1 + z)) ((1 + t)⁻¹ * 1) t :=
      (Real.hasDerivAt_log hne).comp t hadd
    have hsq : HasDerivAt (fun z : ℝ => z ^ 2 / 2) (2 * t / 2) t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    have hraw : HasDerivAt f
        (1 + 2 * t / 2 - (1 * Real.log (1 + t) + (1 + t) * ((1 + t)⁻¹ * 1))) t :=
      (hid.add hsq).sub (hadd.mul hl)
    have heq : 1 + 2 * t / 2 - (1 * Real.log (1 + t) + (1 + t) * ((1 + t)⁻¹ * 1)) =
        t - Real.log (1 + t) := by
      field_simp [hne]
      ring
    rwa [heq] at hraw
  have hmon : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => t - Real.log (1 + t))
      (convex_Ici 0)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
      linarith
  have hf := hmon (show (0 : ℝ) ∈ Set.Ici 0 by simp) hq hq
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hf
  change 0 ≤ q + q ^ 2 / 2 - (1 + q) * Real.log (1 + q) at hf
  exact (div_le_iff₀ (by linarith : 0 < 2 * (1 + q))).mpr (by nlinarith only [hf])

private theorem localEulerGap_one {p : ℕ} (hp : p.Prime) :
    localEulerGap p 1 = (p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹) := by
  let q : ℝ := (p : ℝ)⁻¹
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq1 : q < 1 := (inv_lt_one₀ hp0).mpr hp1
  have hc : Real.log (1 - q ^ 2) = Real.log (1 - q) + Real.log (1 + q) := by
    rw [show 1 - q ^ 2 = (1 - q) * (1 + q) by ring,
      Real.log_mul (by linarith : 1 - q ≠ 0) (by linarith : 1 + q ≠ 0)]
  change (∑ r ∈ range 1, q ^ (r + 1) / (r + 1 : ℕ)) -
    (-Real.log (1 - q) + Real.log (1 - q ^ (1 + 1))) = q - Real.log (1 + q)
  have hprefix : (∑ r ∈ range 1, q ^ (r + 1) / (r + 1 : ℕ)) = q := by
    norm_num [Finset.sum_range_succ]
  rw [hprefix, show (1 + 1 : ℕ) = 2 by decide, hc]
  ring

private theorem localEulerGap_one_lower {p : ℕ} (hp : p.Prime) :
    1 / (2 * (p : ℝ) * ((p : ℝ) + 1)) ≤ localEulerGap p 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : 0 < (p : ℝ) + 1 := by linarith
  rw [localEulerGap_one hp]
  calc
    _ = ((p : ℝ)⁻¹) ^ 2 / (2 * (1 + (p : ℝ)⁻¹)) := by
      have hq : 0 < 1 + (p : ℝ)⁻¹ := by positivity
      field_simp [hp0.ne', hp1.ne', hq.ne']
    _ ≤ _ := log_one_add_gap (inv_nonneg.mpr hp0.le)

/-- Band with the exact lower excluded floor and upper included floor. -/
def primeBand (y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊2 * Real.sqrt y⌋₊ \ Nat.primesLE ⌊Real.sqrt (2 * y)⌋₊

private theorem primeBand_bounds {p : ℕ} {y : ℝ} (hy : 16 ≤ y)
    (hp : p ∈ primeBand y) : p.Prime ∧
      (p : ℝ) ≤ 2 * Real.sqrt y ∧ (p : ℝ) ≤ y / 2 ∧
      2 * y < (p : ℝ) ^ 2 ∧ (p : ℝ) ^ 2 ≤ 4 * y ∧
      (p : ℝ) * ((p : ℝ) + 1) ≤ 8 * y := by
  obtain ⟨hu, hl⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hup, hprime⟩ := Nat.mem_primesLE.mp hu
  have hy0 : 0 ≤ y := by linarith
  have hs0 := Real.sqrt_nonneg y
  have hs4 : 4 ≤ Real.sqrt y := (Real.le_sqrt (by norm_num) hy0).mpr (by norm_num; linarith)
  have hsq := Real.sq_sqrt hy0
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  have hupper : (p : ℝ) ≤ 2 * Real.sqrt y :=
    (Nat.le_floor_iff (by positivity)).mp hup
  have hlNat : ⌊Real.sqrt (2 * y)⌋₊ < p := by
    by_contra! h
    exact hl (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
  have hlReal : Real.sqrt (2 * y) < (p : ℝ) := Nat.lt_of_floor_lt hlNat
  have hlsq : 2 * y < (p : ℝ) ^ 2 := Real.lt_sq_of_sqrt_lt hlReal
  have husq : (p : ℝ) ^ 2 ≤ 4 * y := by
    have hmul := mul_le_mul hupper hupper hp0 (by positivity : 0 ≤ 2 * Real.sqrt y)
    nlinarith only [hmul, hsq]
  have hsY : 2 * Real.sqrt y ≤ y / 2 := by
    nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr hs4) hs0]
  have hpp : (p : ℝ) * ((p : ℝ) + 1) ≤ 8 * y := by
    have h := mul_le_mul_of_nonneg_left (show (p : ℝ) + 1 ≤ 2 * p by linarith) hp0
    nlinarith only [h, husq]
  exact ⟨hprime, hupper, hupper.trans hsY, hlsq, husq, hpp⟩

private theorem first_power_reserve {p : ℕ} {y : ℝ} (hy : 16 ≤ y)
    (hp : p ∈ primeBand y) : 1 / (16 * y) ≤ signedWeight y p := by
  obtain ⟨hprime, _, hpy, _, _, _⟩ := primeBand_bounds hy hp
  have hy0 : 0 < y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog := Real.log_le_log hp0 (show (p : ℝ) ≤ y by linarith)
  have hw : mangoldtWeight p = 1 / (p : ℝ) := by
    simpa [one_div] using mangoldtWeight_prime_pow hprime 0
  have hrate : rate y * vonMangoldt p ≤ 1 / y := by
    rw [rate, vonMangoldt_apply_prime hprime]
    calc
      _ = Real.log p / (y * Real.log y) := by ring
      _ ≤ Real.log y / (y * Real.log y) := div_le_div_of_nonneg_right hlog (by positivity)
      _ = 1 / y := by field_simp [hy0.ne', hly.ne']
  have hstrong : 1 / (y / 2) ≤ 1 / (p : ℝ) := one_div_le_one_div_of_le hp0 hpy
  have heq : 1 / (y / 2) = 2 * (1 / y) := by
    field_simp [hy0.ne']
  rw [heq] at hstrong
  have hweak : 1 / (16 * y) ≤ 1 / y :=
    one_div_le_one_div_of_le hy0 (by linarith)
  unfold signedWeight
  rw [hw]
  linarith only [hrate, hstrong, hweak]

private theorem valuation_one_reserve {p : ℕ} {y : ℝ} (hy : 16 ≤ y)
    (hp : p ∈ primeBand y) : 1 / (16 * y) ≤ localEulerGap p 1 := by
  obtain ⟨hprime, _, _, _, _, hpp⟩ := primeBand_bounds hy hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  calc
    _ ≤ 1 / (2 * (p : ℝ) * ((p : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith only [hpp])
    _ ≤ _ := localEulerGap_one_lower hprime

private theorem second_power_reserve {p : ℕ} {y : ℝ} (hy : 16 ≤ y)
    (hp : p ∈ primeBand y) : 1 / (4 * y) < -signedWeight y (p ^ 2) := by
  obtain ⟨hprime, _, _, hlsq, _, _⟩ := primeBand_bounds hy hp
  have hy0 : 0 < y := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hpSq : y < (p : ℝ) ^ 2 := by linarith
  have hlog := Real.log_lt_log hy0 hpSq
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hrate : 1 / (2 * y) < rate y * vonMangoldt (p ^ 2) := by
    rw [rate, vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0), vonMangoldt_apply_prime hprime]
    calc
      _ = (Real.log y / 2) / (y * Real.log y) := by
        field_simp [hy0.ne', hly.ne']
      _ < Real.log p / (y * Real.log y) :=
        (div_lt_div_iff_of_pos_right (mul_pos hy0 hly)).mpr (by linarith)
      _ = _ := by ring
  have hw : mangoldtWeight (p ^ 2) = 1 / (2 * (p : ℝ) ^ 2) := by
    have h := mangoldtWeight_prime_pow hprime 1
    change mangoldtWeight (p ^ 2) = (p : ℝ)⁻¹ ^ 2 / (2 : ℝ) at h
    rw [h]
    field_simp [hp0.ne']
  have hwt : mangoldtWeight (p ^ 2) < 1 / (4 * y) := by
    rw [hw]
    exact one_div_lt_one_div_of_lt (by linarith : 0 < 4 * y) (by linarith)
  have heq : 1 / (2 * y) = 2 * (1 / (4 * y)) := by
    field_simp [hy0.ne']
    ring
  rw [heq] at hrate
  unfold signedWeight
  linarith only [hrate, hwt]

/-- Transport a lower bound from distinct chosen slots into a nonnegative sum.
The injectivity hypothesis is used in sum_image and the containment in the
subset comparison. The three valuation classes have separate parent sums. The first-power image is
contained in cutoff y \ n.divisors, the square image in n.divisors \ cutoff y.
These sets are disjoint, and the square map is injective on natural numbers.
The Euler-gap slots are indexed by distinct primes in n.primeFactors. -/
private theorem card_reserve_of_injOn (s t : Finset ℕ) (f : ℕ → ℕ) (w : ℕ → ℝ)
    (c : ℝ) (hmap : ∀ p ∈ s, f p ∈ t)
    (hinj : Set.InjOn f (↑s : Set ℕ)) (hpay : ∀ p ∈ s, c ≤ w (f p))
    (hnonneg : ∀ d ∈ t, 0 ≤ w d) :
    (s.card : ℝ) * c ≤ ∑ d ∈ t, w d := by
  classical
  have hsub : s.image f ⊆ t := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact hmap p hp
  calc
    _ = ∑ _p ∈ s, c := by simp [nsmul_eq_mul]
    _ ≤ ∑ p ∈ s, w (f p) := sum_le_sum hpay
    _ = ∑ d ∈ s.image f, w d :=
      (sum_image (fun a ha b hb he => hinj ha hb he)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun d hd _ => hnonneg d hd)

/-- Unconditional reserve for every prime of the band, including missing primes.
The three classes m=0, m=1, m≥2 use, respectively, missing first-power
slots, local Euler gaps, and extra second-power slots. -/
theorem primeBand_reserve_le_robinLogSlack {n : ℕ}
    (hy : 16 ≤ Real.log (n : ℝ)) :
    ((primeBand (Real.log (n : ℝ))).card : ℝ) / (16 * Real.log (n : ℝ)) ≤
      robinLogMargin n - weightedTail psiErrorKernel (Real.log (n : ℝ)) := by
  classical
  let y : ℝ := Real.log (n : ℝ)
  change 16 ≤ y at hy
  have hn : 0 < n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    norm_num [y, hn0] at hy
  have hy2 : 2 ≤ y := by linarith
  let b := primeBand y
  let m : ℕ → ℕ := fun p => n.factorization p
  let b0 := b.filter (fun p => m p = 0)
  let bp := b.filter (fun p => m p ≠ 0)
  let b1 := bp.filter (fun p => m p = 1)
  let b2 := bp.filter (fun p => m p ≠ 1)
  let c : ℝ := 1 / (16 * y)
  have hcards : b0.card + b1.card + b2.card = b.card := by
    have h0 := card_filter_add_card_filter_not (s := b) (fun p => m p = 0)
    have h1 := card_filter_add_card_filter_not (s := bp) (fun p => m p = 1)
    change b0.card + bp.card = b.card at h0
    change b1.card + b2.card = bp.card at h1
    omega
  have h0 : (b0.card : ℝ) * c ≤
      ∑ d ∈ cutoff y \ n.divisors, signedWeight y d := by
    apply card_reserve_of_injOn b0 (cutoff y \ n.divisors) id (signedWeight y) c
    · intro p hp
      obtain ⟨hpb, hm0⟩ := mem_filter.mp hp
      obtain ⟨hprime, _, hpy, _, _, _⟩ := primeBand_bounds hy hpb
      apply mem_sdiff.mpr
      refine ⟨mem_Ioc.mpr ⟨hprime.pos, Nat.le_floor (show (p : ℝ) ≤ y by linarith)⟩, ?_⟩
      intro hdiv
      have hpos := hprime.factorization_pos_of_dvd hn.ne' (Nat.mem_divisors.mp hdiv).1
      change n.factorization p = 0 at hm0
      omega
    · intro a ha b hb h
      exact h
    · intro p hp
      exact first_power_reserve hy (mem_filter.mp hp).1
    · intro d hd
      exact signedWeight_nonneg hy2 (mem_sdiff.mp hd).1
  have h1 : (b1.card : ℝ) * c ≤
      ∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p) := by
    apply card_reserve_of_injOn b1 n.primeFactors id
      (fun p => localEulerGap p (n.factorization p)) c
    · intro p hp
      obtain ⟨hpos, hm1⟩ := mem_filter.mp hp
      have hprime := (primeBand_bounds hy (mem_filter.mp hpos).1).1
      apply Nat.mem_primeFactors.mpr
      refine ⟨hprime, ?_, hn.ne'⟩
      change p ∣ n
      by_contra hnot
      have hz := Nat.factorization_eq_zero_of_not_dvd hnot
      change n.factorization p = 1 at hm1
      omega
    · intro a ha b hb h
      exact h
    · intro p hp
      obtain ⟨hpos, hm1⟩ := mem_filter.mp hp
      change n.factorization p = 1 at hm1
      change c ≤ localEulerGap p (n.factorization p)
      rw [hm1]
      exact valuation_one_reserve hy (mem_filter.mp hpos).1
    · intro p hp
      exact localEulerGap_nonneg (Nat.prime_of_mem_primeFactors hp)
  have h2 : (b2.card : ℝ) * c ≤
      ∑ d ∈ n.divisors \ cutoff y, -signedWeight y d := by
    apply card_reserve_of_injOn b2 (n.divisors \ cutoff y) (fun p => p ^ 2)
      (fun d => -signedWeight y d) c
    · intro p hp
      obtain ⟨hpos, hmne1⟩ := mem_filter.mp hp
      obtain ⟨hpb, hmne0⟩ := mem_filter.mp hpos
      obtain ⟨hprime, _, _, hlsq, _, _⟩ := primeBand_bounds hy hpb
      change n.factorization p ≠ 0 at hmne0
      change n.factorization p ≠ 1 at hmne1
      apply mem_sdiff.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨(hprime.pow_dvd_iff_le_factorization hn.ne').mpr
        (by omega), hn.ne'⟩, ?_⟩
      intro hcut
      have hle := (Nat.le_floor_iff (by linarith : 0 ≤ y)).mp (mem_Ioc.mp hcut).2
      rw [Nat.cast_pow] at hle
      linarith
    · intro a ha b hb he
      exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) he
    · intro p hp
      have hr := second_power_reserve hy (mem_filter.mp (mem_filter.mp hp).1).1
      have hc : c ≤ 1 / (4 * y) := by
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      exact hc.trans hr.le
    · intro d hd
      exact neg_signedWeight_nonneg hy2 (mem_sdiff.mp hd).1 (mem_sdiff.mp hd).2
  have hcardR : (b0.card : ℝ) + (b1.card : ℝ) + (b2.card : ℝ) = (b.card : ℝ) := by
    exact_mod_cast hcards
  have htotal : (b.card : ℝ) * c ≤
      (∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p)) +
      (∑ d ∈ cutoff y \ n.divisors, signedWeight y d) +
      (∑ d ∈ n.divisors \ cutoff y, -signedWeight y d) := by
    rw [← hcardR, add_mul, add_mul]
    linarith only [h0, h1, h2]
  have hslack := robin_slack_eq hn (show 2 ≤ Real.log (n : ℝ) from hy2)
  change robinLogMargin n - weightedTail psiErrorKernel y =
      (∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p)) +
      (∑ d ∈ cutoff y \ n.divisors, signedWeight y d) +
      (∑ d ∈ n.divisors \ cutoff y, -signedWeight y d) at hslack
  change (b.card : ℝ) / (16 * y) ≤ robinLogMargin n - weightedTail psiErrorKernel y
  calc
    _ = (b.card : ℝ) * c := div_eq_mul_one_div _ _
    _ ≤ (∑ p ∈ n.primeFactors, localEulerGap p (n.factorization p)) +
        (∑ d ∈ cutoff y \ n.divisors, signedWeight y d) +
        (∑ d ∈ n.divisors \ cutoff y, -signedWeight y d) := htotal
    _ = _ := hslack.symm

#print axioms primeBand_reserve_le_robinLogSlack

end D5.S3.Arith.Robin.WeightedTail.PrimeBandReserve
