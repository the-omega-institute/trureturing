/- GID: D5/S3/Arith/Partitions/SupernormSizeAsymptotic
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/SupernormSizeAsymptotic
   mirror-E: none(waiver:symbolic-limit-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Reciprocal prime supernorms on partitions of fixed size. -/

import D5.S3.Combinatorics.Partitions.OverpartitionThreshold
import D5.S3.Combinatorics.Partitions.PositiveEnergyPartition
import D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder
import D5.S3.Weil.Mertens.Third
import D5.S3.Arith.Divisors.DivisorSubpower
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Filter Real
open D5.S3.Arith.Robin.PriceRecord
open scoped Topology BigOperators
namespace D5.S3.Arith.Partitions.SupernormSizeAsymptotic
/-- The prime attached to a positive part, with indexing starting at one. -/
def partPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)
private lemma partPrime_pos (k : ℕ) : 0 < partPrime k :=
  (Nat.prime_nth_prime (k - 1)).pos
/-- The source supernorm is the product of the primes indexed by all parts. -/
def supernorm {n : ℕ} (p : n.Partition) : ℕ :=
  (p.parts.map (fun k => Nat.nth Nat.Prime (k - 1))).prod
/-- The reciprocal supernorm sum over the complete size ensemble. -/
def Wsize (n : ℕ) : ℝ := ∑ p : n.Partition, 1 / (supernorm p : ℝ)
private lemma Wsize_nonneg (n : ℕ) : 0 ≤ Wsize n :=
  sum_nonneg fun _ _ => by positivity
private lemma partPrime_top :
    Tendsto (fun n : ℕ => (partPrime n : ℝ)) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  exact hp.comp (tendsto_sub_atTop_nat 1)
private lemma partPrime_count (n : ℕ) (hn : 0 < n) :
    QuantitativePrimeAbel.primeCount (partPrime n : ℝ) = n := by
  have hc : Nat.primeCounting (partPrime n) = n := by
    change Nat.count Nat.Prime (Nat.nth Nat.Prime (n - 1) + 1) = n
    rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime,
      Nat.sub_add_cancel hn]
  simp only [QuantitativePrimeAbel.primeCount, Nat.floor_natCast, hc]
private lemma partPrime_normalized :
    Tendsto (fun n : ℕ => (n : ℝ) * log (partPrime n) / partPrime n)
      atTop (𝓝 1) := by
  have h := PrimeBoundarySecondOrder.pi_normalized.comp partPrime_top
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change log (partPrime n) *
    QuantitativePrimeAbel.primeCount
      (partPrime n : ℝ) / partPrime n = _
  rw [partPrime_count n hn]
  ring
private lemma log_index_div_log_prime :
    Tendsto (fun n : ℕ => log (n : ℝ) / log (partPrime n)) atTop (𝓝 1) := by
  have hL : Tendsto (fun n : ℕ => log (partPrime n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp partPrime_top
  have hs : Tendsto (fun n : ℕ => log (log (partPrime n)) /
      log (partPrime n)) atTop (𝓝 0) :=
    (isLittleO_log_id_atTop.comp_tendsto hL).tendsto_div_nhds_zero
  have he : Tendsto (fun n : ℕ =>
      log ((n : ℝ) * log (partPrime n) / partPrime n) /
        log (partPrime n)) atTop (𝓝 0) :=
    (partPrime_normalized.log one_ne_zero).div_atTop hL
  have h := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub hs).add he
  norm_num only [sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp1 : (1 : ℝ) < partPrime n := by
    exact_mod_cast (Nat.prime_nth_prime (n - 1)).one_lt
  have hp0 : (0 : ℝ) < partPrime n := lt_trans zero_lt_one hp1
  have hLp : 0 < log (partPrime n : ℝ) := log_pos hp1
  change 1 - log (log (partPrime n)) / log (partPrime n) +
    log ((n : ℝ) * log (partPrime n) / partPrime n) /
      log (partPrime n) = log (n : ℝ) / log (partPrime n)
  rw [log_div (mul_ne_zero hn0.ne' hLp.ne') hp0.ne', log_mul hn0.ne' hLp.ne']
  field_simp [hLp.ne']
  <;> ring
private lemma partPrime_log_ratio :
    Tendsto (fun n : ℕ => log (partPrime n) / log (n : ℝ)) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using log_index_div_log_prime.inv₀ one_ne_zero
private lemma partPrime_asymptotic :
    Tendsto (fun n : ℕ => (n : ℝ) * log n / partPrime n) atTop (𝓝 1) := by
  have h := partPrime_normalized.mul log_index_div_log_prime
  norm_num only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hp1 : (1 : ℝ) < partPrime n := by
    exact_mod_cast (Nat.prime_nth_prime (n - 1)).one_lt
  have hLp : log (partPrime n : ℝ) ≠ 0 := (log_pos hp1).ne'
  change (n : ℝ) * log (partPrime n) / partPrime n *
    (log n / log (partPrime n)) = (n : ℝ) * log n / partPrime n
  field_simp [hLp]

open D5.S3.Combinatorics.Partitions.OverpartitionThreshold (shiftEquiv)
private def thresholdWeight (n d r : ℕ) : ℝ :=
  ∑ p : n.Partition, if r ≤ p.parts.count d then 1 / (supernorm p : ℝ) else 0
private lemma threshold_shift {n d r : ℕ} (hd : 0 < d) (hn : r * d ≤ n) :
    thresholdWeight n d r = (1 / (partPrime d : ℝ) ^ r) * Wsize (n - r * d) := by
  classical
  let e := shiftEquiv n r d hd hn
  calc
    _ = ∑ p : {p : n.Partition // r ≤ p.parts.count d},
        1 / (supernorm p.1 : ℝ) := by
      rw [← Finset.sum_subtype (p := fun p : n.Partition => r ≤ p.parts.count d)
        (Finset.univ.filter (fun p : n.Partition => r ≤ p.parts.count d))
        (by simp) (fun p => 1 / (supernorm p : ℝ))]
      simp [thresholdWeight, Finset.sum_filter]
    _ = ∑ p : (n - r * d).Partition, 1 / (supernorm (e.symm p).1 : ℝ) := by
      rw [← e.symm.sum_comp]
    _ = _ := by
      rw [Wsize, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have hs : supernorm (e.symm p).1 = supernorm p * partPrime d ^ r := by
        simp [e, supernorm, shiftEquiv, partPrime]
      rw [hs, Nat.cast_mul, Nat.cast_pow]
      simp only [one_div, mul_inv_rev]
private lemma multiplicity_size_bound {n : ℕ} (p : n.Partition) (d : ℕ) :
    p.parts.count d * d ≤ n := by
  have hle : Multiset.replicate (p.parts.count d) d ≤ p.parts :=
    Multiset.le_count_iff_replicate_le.mp le_rfl
  have he := congrArg Multiset.sum (tsub_add_cancel_of_le hle)
  simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, p.parts_sum] at he
  omega
private lemma multiplicity_threshold_sum {n d : ℕ} (hd : 0 < d)
    (p : n.Partition) :
    (p.parts.count d : ℝ) * (1 / (supernorm p : ℝ)) =
      ∑ r ∈ Icc 1 (n / d),
        if r ≤ p.parts.count d then 1 / (supernorm p : ℝ) else 0 := by
  have hc : p.parts.count d ≤ n / d :=
    (Nat.le_div_iff_mul_le hd).mpr (multiplicity_size_bound p d)
  have hf : (Icc 1 (n / d)).filter (fun r => r ≤ p.parts.count d) =
      Icc 1 (p.parts.count d) := by
    ext r
    simp only [mem_filter, mem_Icc]
    omega
  rw [← Finset.sum_filter, hf]
  simp [Nat.card_Icc]
private lemma marked_part_sum {n d : ℕ} (hd : 0 < d) :
    (∑ p : n.Partition, (p.parts.count d : ℝ) * (1 / (supernorm p : ℝ))) =
      ∑ r ∈ Icc 1 (n / d),
        (1 / (partPrime d : ℝ) ^ r) * Wsize (n - r * d) := by
  classical
  simp_rw [multiplicity_threshold_sum hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  exact threshold_shift hd ((Nat.le_div_iff_mul_le hd).mp (mem_Icc.mp hr).2)
private lemma marked_part_recurrence (n : ℕ) :
    (n : ℝ) * Wsize n =
      ∑ d ∈ Icc 1 n, ∑ r ∈ Icc 1 (n / d),
        (d : ℝ) / (partPrime d : ℝ) ^ r * Wsize (n - r * d) := by
  classical
  have hdegree (p : n.Partition) :
      (∑ d ∈ Icc 1 n, d * p.parts.count d) = n := by
    have he := (Finset.mem_finsuppAntidiag.mp
      p.toFinsuppAntidiag_mem_finsuppAntidiag).1
    change (∑ d ∈ Icc 1 n, p.parts.count d * d) = n at he
    simpa only [mul_comm] using he
  have hdegree_real (p : n.Partition) :
      (∑ d ∈ Icc 1 n, (d : ℝ) * p.parts.count d) = n := by
    exact_mod_cast hdegree p
  calc
    _ = ∑ p : n.Partition,
        (∑ d ∈ Icc 1 n, (d : ℝ) * p.parts.count d) *
          (1 / (supernorm p : ℝ)) := by
      simp only [hdegree_real, Wsize, Finset.mul_sum]
    _ = ∑ d ∈ Icc 1 n, (d : ℝ) *
        ∑ p : n.Partition, (p.parts.count d : ℝ) * (1 / (supernorm p : ℝ)) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [marked_part_sum (mem_Icc.mp hd).1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

private def E (m : ℕ) : ℝ :=
  ∏ j ∈ Icc 1 m, (1 - (partPrime j : ℝ)⁻¹)⁻¹
private lemma E_eq_prime_product {m : ℕ} (hm : 1 ≤ m) :
    E m = (∏ p ∈ Ioc 0 (partPrime m) with p.Prime,
      (1 - (1 : ℝ) / p))⁻¹ := by
  classical
  rw [← prod_inv_distrib]
  unfold E
  refine prod_bij (fun j _ => partPrime j) ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hj1, hjm⟩ := mem_Icc.mp hj
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨partPrime_pos j, ?_⟩, Nat.prime_nth_prime (j - 1)⟩
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
      (Nat.sub_le_sub_right hjm 1)
  · intro i hi j hj hij
    have he := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    have hi1 := (mem_Icc.mp hi).1
    have hj1 := (mem_Icc.mp hj).1
    omega
  · intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have hp_le := (mem_Ioc.mp hpI).2
    have hp_nth : Nat.nth Nat.Prime (Nat.primeCounting' p) = p :=
      Nat.nth_count hpp
    have hindex : Nat.primeCounting' p ≤ m - 1 := by
      apply (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mp
      rw [hp_nth]
      exact hp_le
    refine ⟨Nat.primeCounting' p + 1, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa only [partPrime, Nat.add_sub_cancel] using hp_nth
  · intro j hj
    simp only [one_div]
private lemma E_log_limit :
    Tendsto (fun m : ℕ => E m / log m)
      atTop (𝓝 (exp eulerMascheroniConstant)) := by
  have hne : ∀ᶠ x : ℝ in atTop,
      (exp (-eulerMascheroniConstant) / log x)⁻¹ ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact inv_ne_zero (div_ne_zero (exp_ne_zero _) (log_pos hx).ne')
  have hraw := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp Mertens.E₃.bound''.inv
  have hreal : Tendsto (fun x : ℝ =>
      (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹ / log x)
      atTop (𝓝 (exp eulerMascheroniConstant)) := by
    have h := hraw.mul_const (exp eulerMascheroniConstant)
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    change ((∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹ /
      (exp (-eulerMascheroniConstant) / log x)⁻¹) *
        exp eulerMascheroniConstant = _
    rw [exp_neg]
    field_simp [(log_pos hx).ne', exp_ne_zero eulerMascheroniConstant]
  have h := (hreal.comp partPrime_top).mul partPrime_log_ratio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  have hp1 : (1 : ℝ) < partPrime m := by
    exact_mod_cast (Nat.prime_nth_prime (m - 1)).one_lt
  have hLp : log (partPrime m : ℝ) ≠ 0 := (log_pos hp1).ne'
  change ((∏ p ∈ Ioc 0 ⌊(partPrime m : ℝ)⌋₊ with p.Prime,
    (1 - (1 : ℝ) / p))⁻¹ / log (partPrime m)) *
      (log (partPrime m) / log m) = E m / log m
  rw [Nat.floor_natCast, ← E_eq_prime_product (by omega : 1 ≤ m)]
  field_simp [hLp]

private def b (j : ℕ) : ℝ :=
  ∑ d ∈ j.divisors, (d : ℝ) / (partPrime d : ℝ) ^ (j / d)
private def kernelR (j : ℕ) : ℝ :=
  ∑ d ∈ j.divisors.erase j, (d : ℝ) / (partPrime d : ℝ) ^ (j / d)
private lemma b_decomposition {j : ℕ} (hj : 0 < j) :
    b j = (j : ℝ) / partPrime j + kernelR j := by
  simpa [b, kernelR, Nat.div_self hj, add_comm] using
    (sum_erase_add j.divisors (fun d =>
      (d : ℝ) / (partPrime d : ℝ) ^ (j / d)) (Nat.mem_divisors_self j hj.ne')).symm
private lemma geometric_quadratic_bound {d r : ℕ} (hd : 1 ≤ d) (hr : 2 ≤ r) :
    (r : ℝ) * (d : ℝ) ^ 2 ≤ 2 * ((d : ℝ) + 1) ^ r := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain rfl | hr3 := hr.eq_or_lt
  · norm_num; nlinarith
  have hb := pow_add_mul_le_add_pow (by positivity : (0 : ℝ) ≤ d)
    (by positivity : (0 : ℝ) ≤ 2 * d + 1) r
  have hp : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ (r - 1) :=
    pow_le_pow_right₀ hdR (by omega)
  nlinarith [mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg r),
    pow_nonneg (by positivity : (0 : ℝ) ≤ d) r]
private lemma proper_divisor_kernel_bound {j d : ℕ} (hj : 0 < j)
    (hd : d ∈ j.divisors.erase j) :
    (d : ℝ) / (partPrime d : ℝ) ^ (j / d) ≤ 2 / (j : ℝ) := by
  obtain ⟨hdj, hdmem⟩ := mem_erase.mp hd
  have hdpos := Nat.pos_of_mem_divisors hdmem
  have hdvd := (Nat.mem_divisors.mp hdmem).1
  have hmul := Nat.div_mul_cancel hdvd
  have hdivpos := Nat.div_pos (Nat.le_of_dvd hj hdvd) hdpos
  have hr : 2 ≤ j / d := by
    by_contra hr
    have : j / d = 1 := by omega
    simp_all
  have hp : (d : ℝ) + 1 ≤ partPrime d := by
    have h := Nat.add_two_le_nth_prime (d - 1)
    exact_mod_cast (show d + 1 ≤ partPrime d by dsimp [partPrime]; omega)
  have hb := (geometric_quadratic_bound (by omega : 1 ≤ d) hr).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hp _) (by norm_num))
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hpR : (0 : ℝ) < partPrime d := by exact_mod_cast partPrime_pos d
  apply (div_le_div_iff₀ (pow_pos hpR _) hjR).mpr
  have he : (j : ℝ) = (j / d : ℕ) * (d : ℝ) := by exact_mod_cast hmul.symm
  rw [he]
  nlinarith
private lemma kernelR_sqrt_bound : ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 0 < j →
    kernelR j ≤ 2 * C / sqrt j := by
  obtain ⟨C, hC, hbound⟩ :=
    D5.S3.Arith.Divisors.DivisorSubpower.card_divisors_subpower
      (1 / 2 : ℝ) (by norm_num)
  refine ⟨C, hC, fun j hj => ?_⟩
  calc
    kernelR j ≤ ((j.divisors.erase j).card : ℝ) * (2 / j) := by
      simpa only [kernelR, sum_const, nsmul_eq_mul] using
        (sum_le_sum fun d hd => proper_divisor_kernel_bound hj hd)
    _ ≤ (j.divisors.card : ℝ) * (2 / j) := by
      gcongr
      exact erase_subset j j.divisors
    _ ≤ (C * sqrt j) * (2 / j) := by
      gcongr
      simpa only [sqrt_eq_rpow] using hbound j hj.ne'
    _ = 2 * C / sqrt j := by
      calc
        _ = (2 * C) * (sqrt j / j) := by ring
        _ = _ := by rw [sqrt_div_self, div_eq_mul_inv]
private lemma kernel_log_limit :
    Tendsto (fun j : ℕ => b j * log j) atTop (𝓝 1) := by
  obtain ⟨C, hC, hbound⟩ := kernelR_sqrt_bound
  have hupper : Tendsto (fun j : ℕ => 2 * C * (log j / sqrt j))
      atTop (𝓝 0) := by
    have hl : Tendsto (fun x : ℝ => log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have h := hl.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
    simpa only [← sqrt_eq_rpow, mul_zero, Function.comp_apply] using h.const_mul (2 * C)
  have hR : Tendsto (fun j : ℕ => kernelR j * log j) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hupper
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
      exact mul_nonneg (sum_nonneg fun d _ => by positivity) (log_nonneg (by exact_mod_cast hj))
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
      have h := mul_le_mul_of_nonneg_right (hbound j (by omega))
        (log_nonneg (show (1 : ℝ) ≤ j by exact_mod_cast hj))
      convert h using 1 <;> ring
  have h := partPrime_asymptotic.add hR
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
  rw [b_decomposition (by omega : 0 < j)]
  ring

private def cutoff (n : ℕ) : ℕ := ⌊(n : ℝ) / log n⌋₊
private lemma cutoff_scale_top :
    Tendsto (fun n : ℕ => (n : ℝ) / log n) atTop atTop := by
  have h := isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have hp : ∀ᶠ n : ℕ in atTop, 0 < log (n : ℝ) / n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact div_pos (log_pos hn1) (lt_trans zero_lt_one hn1)
  have hw := tendsto_nhdsWithin_iff.mpr ⟨h, hp⟩
  simpa only [Pi.inv_def, Function.comp_apply, id_eq, inv_div] using
    hw.inv_tendsto_nhdsGT_zero
private lemma cutoff_top : Tendsto cutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp cutoff_scale_top
private lemma cutoff_ratio :
    Tendsto (fun n : ℕ => (cutoff n : ℝ) / ((n : ℝ) / log n)) atTop (𝓝 1) :=
  tendsto_nat_floor_div_atTop.comp cutoff_scale_top
private lemma cutoff_small :
    Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0) := by
  have h := cutoff_ratio.div_atTop
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  dsimp
  field_simp [(log_pos hn1).ne', (lt_trans zero_lt_one hn1).ne']
private lemma cutoff_log_ratio :
    Tendsto (fun n : ℕ => log (cutoff n) / log n) atTop (𝓝 1) := by
  have hlogn := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have herror := (cutoff_ratio.log one_ne_zero).div_atTop hlogn
  have hloglog := isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogn
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := (hc.sub hloglog).add herror
  norm_num only [sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), cutoff_top.eventually_ge_atTop 1]
    with n hn hc
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hc0 : (0 : ℝ) < cutoff n := by exact_mod_cast (by omega : 0 < cutoff n)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hn1
  have hL : 0 < log (n : ℝ) := log_pos hn1
  change 1 - log (log (n : ℝ)) / log n +
    log ((cutoff n : ℝ) / ((n : ℝ) / log n)) / log n = _
  rw [log_div hc0.ne' (div_pos hn0 hL).ne', log_div hn0.ne' hL.ne']
  field_simp [hL.ne']
  <;> ring

open D5.S3.VertexAlgebra.PolynomialFockLZeroSpectrum (energy EnergyFiber)
open D5.S3.VertexAlgebra.PolynomialFockCharacter (energyFiberEquivPartition)
private def occupation (m : ℕ) (x : Fin m → ℕ) : ℕ →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm x).embDomain ⟨Fin.val, Fin.val_injective⟩
private lemma occupation_injective (m : ℕ) : Function.Injective (occupation m) := by
  intro x y h
  exact Finsupp.equivFunOnFinite.symm.injective
    (Finsupp.embDomain_injective ⟨Fin.val, Fin.val_injective⟩ h)
private lemma occupation_energy (m : ℕ) (x : Fin m → ℕ) :
    energy (occupation m x) = ∑ i : Fin m, (i.val + 1) * x i := by
  simp only [energy, occupation, Finsupp.sum_embDomain]
  exact Finsupp.sum_fintype _ _ (fun _ => mul_zero _)
private def occupationPartition (m : ℕ) (x : Fin m → ℕ) :
    (energy (occupation m x)).Partition :=
  energyFiberEquivPartition _ ⟨occupation m x, rfl⟩
private lemma occupationPartition_parts (m : ℕ) (x : Fin m → ℕ) :
    (occupationPartition m x).parts = (occupation m x).toMultiset.map Nat.succ := by
  rfl
private lemma supernorm_occupation (m : ℕ) (x : Fin m → ℕ) :
    supernorm (occupationPartition m x) =
      ∏ i : Fin m, partPrime (i.val + 1) ^ x i := by
  rw [supernorm, occupationPartition_parts, Multiset.map_map]
  rw [Finset.prod_multiset_map_count]
  simp only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset]
  change (occupation m x).prod (fun i k => partPrime (i + 1) ^ k) = _
  rw [occupation, Finsupp.prod_embDomain]
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
private abbrev cumulativePartition (n : ℕ) := Σ k : Fin (n + 1), k.val.Partition
private def goodOccupationToPartition {m n : ℕ}
    (x : {x : Fin m → ℕ // energy (occupation m x) ≤ n}) : cumulativePartition n :=
  ⟨⟨energy (occupation m x.1), Nat.lt_succ_iff.mpr x.2⟩,
    occupationPartition m x.1⟩
private lemma goodOccupationToPartition_injective (m n : ℕ) :
    Function.Injective (@goodOccupationToPartition m n) := by
  intro x y h
  apply Subtype.ext
  apply occupation_injective m
  have hp := congrArg (fun p : cumulativePartition n => p.2.parts) h
  change (occupation m x.1).toMultiset.map Nat.succ =
    (occupation m y.1).toMultiset.map Nat.succ at hp
  have he := Multiset.map_injective Nat.succ_injective hp
  simpa only [Finsupp.toMultiset_toFinsupp] using congrArg Multiset.toFinsupp he
private def occupationWeight (m : ℕ) (x : Fin m → ℕ) : ℝ :=
  ∏ i : Fin m, (partPrime (i.val + 1) : ℝ)⁻¹ ^ x i
private def occupationBox (m L : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ => range L)
private lemma occupationWeight_nonneg (m : ℕ) (x : Fin m → ℕ) :
    0 ≤ occupationWeight m x := by
  exact Finset.prod_nonneg fun _ _ => by positivity
private lemma occupationWeight_eq (m : ℕ) (x : Fin m → ℕ) :
    occupationWeight m x = 1 / (supernorm (occupationPartition m x) : ℝ) := by
  rw [supernorm_occupation]
  simp only [occupationWeight, Nat.cast_prod, Nat.cast_pow, one_div,
    Finset.prod_inv_distrib, inv_pow]
private lemma box_mass_product (m L : ℕ) :
    (∑ x ∈ occupationBox m L, occupationWeight m x) =
      ∏ i : Fin m, ∑ r ∈ range L, (partPrime (i.val + 1) : ℝ)⁻¹ ^ r := by
  exact (Finset.prod_univ_sum (fun _ : Fin m => range L)
    (fun i r => (partPrime (i.val + 1) : ℝ)⁻¹ ^ r)).symm
private lemma prime_reciprocal_lt_one (k : ℕ) :
    (partPrime k : ℝ)⁻¹ < 1 := by
  have hp : (1 : ℝ) < partPrime k := by
    exact_mod_cast (Nat.prime_nth_prime (k - 1)).one_lt
  exact inv_lt_one_of_one_lt₀ hp
private lemma box_mass_limit (m : ℕ) :
    Tendsto (fun L => ∑ x ∈ occupationBox m L, occupationWeight m x) atTop
      (𝓝 (∏ i : Fin m, (1 - (partPrime (i.val + 1) : ℝ)⁻¹)⁻¹)) := by
  simp_rw [box_mass_product]
  apply tendsto_finsetProd
  intro i _
  exact (hasSum_geometric_of_lt_one (by positivity)
    (prime_reciprocal_lt_one _)).tendsto_sum_nat
private lemma finite_markov {α : Type*} (s : Finset α) (w : α → ℝ)
    (e : α → ℕ) {n : ℕ} (hn : 0 < n) (hw : ∀ x ∈ s, 0 ≤ w x) :
    (∑ x ∈ s, w x) - (∑ x ∈ s, (e x : ℝ) * w x) / n ≤
      ∑ x ∈ s.filter (fun x => e x ≤ n), w x := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : e x ≤ n
  · rw [if_pos he]
    exact sub_le_self _ (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hw x hx)) hnR.le)
  · rw [if_neg he]
    have hen : (n : ℝ) ≤ e x := by exact_mod_cast (show n ≤ e x by omega)
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hen (hw x hx)]
private lemma E_eq_fin (m : ℕ) :
    E m = ∏ i : Fin m, (1 - (partPrime (i.val + 1) : ℝ)⁻¹)⁻¹ := by
  calc
    E m = ∏ j ∈ range m, (1 - (partPrime (j + 1) : ℝ)⁻¹)⁻¹ := by
      rw [E, ← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
      simp [Nat.add_comm]
    _ = _ := Finset.prod_range _
private lemma geometric_partial (k L : ℕ) :
    (∑ r ∈ range L, (partPrime k : ℝ)⁻¹ ^ r) ≤
      (1 - (partPrime k : ℝ)⁻¹)⁻¹ := by
  exact sum_le_hasSum (range L) (fun r _ => by positivity)
    (hasSum_geometric_of_lt_one (by positivity) (prime_reciprocal_lt_one k))
private lemma weighted_geometric_partial (k L : ℕ) :
    (∑ r ∈ range L, ((k : ℝ) + 1) * (r : ℝ) *
      (partPrime (k + 1) : ℝ)⁻¹ ^ r) ≤
        (1 - (partPrime (k + 1) : ℝ)⁻¹)⁻¹ := by
  let q : ℝ := (partPrime (k + 1) : ℝ)⁻¹
  have hp : (k : ℝ) + 2 ≤ partPrime (k + 1) := by
    exact_mod_cast Nat.add_two_le_nth_prime k
  have hp0 : (0 : ℝ) < partPrime (k + 1) := by
    exact_mod_cast partPrime_pos (k + 1)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := prime_reciprocal_lt_one (k + 1)
  have hd : 0 < 1 - q := by linarith
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one
    (r := q) (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)).mul_left
      ((k : ℝ) + 1)
  have hb := sum_le_hasSum (range L) (fun r _ => by positivity) hs
  apply (show (∑ r ∈ range L, ((k : ℝ) + 1) * (r : ℝ) * q ^ r) ≤
    ((k : ℝ) + 1) * (q / (1 - q) ^ 2) by simpa only [mul_assoc] using hb).trans
  have hc : ((k : ℝ) + 2) * q ≤ 1 :=
    (mul_inv_le_iff₀ hp0).mpr (by simpa using hp)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have he : (1 - q)⁻¹ * (1 - q) ^ 2 = 1 - q := by field_simp [hd.ne']
  rw [he]
  linarith
private lemma box_coordinate_moment (m L : ℕ) (i : Fin m) :
    (∑ x ∈ occupationBox m L,
      (((i.val : ℝ) + 1) * (x i : ℝ)) * occupationWeight m x) ≤ E m := by
  classical
  let f : Fin m → ℕ → ℝ := fun j r =>
    (if j = i then ((j.val : ℝ) + 1) * (r : ℝ) else 1) *
      (partPrime (j.val + 1) : ℝ)⁻¹ ^ r
  have hprod (x : Fin m → ℕ) :
      (∏ j : Fin m, f j (x j)) =
        (((i.val : ℝ) + 1) * (x i : ℝ)) * occupationWeight m x := by
    simp only [f, occupationWeight, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  calc
    _ = ∑ x ∈ occupationBox m L, ∏ j : Fin m, f j (x j) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (hprod x).symm
    _ = ∏ j : Fin m, ∑ r ∈ range L, f j r :=
      (Finset.prod_univ_sum (fun _ : Fin m => range L) f).symm
    _ ≤ ∏ j : Fin m, (1 - (partPrime (j.val + 1) : ℝ)⁻¹)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro j _
        apply Finset.sum_nonneg
        intro r _
        dsimp [f]
        split_ifs <;> positivity
      · intro j _
        by_cases hji : j = i
        · simp only [f, if_pos hji]
          exact weighted_geometric_partial j.val L
        · simp only [f, if_neg hji, one_mul]
          exact geometric_partial (j.val + 1) L
    _ = E m := (E_eq_fin m).symm
private lemma box_moment_bound (m L : ℕ) :
    (∑ x ∈ occupationBox m L,
      (energy (occupation m x) : ℝ) * occupationWeight m x) ≤ (m : ℝ) * E m := by
  have he (x : Fin m → ℕ) :
      (energy (occupation m x) : ℝ) =
        ∑ i : Fin m, ((i.val : ℝ) + 1) * (x i : ℝ) := by
    exact_mod_cast occupation_energy m x
  simp_rw [he, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : Fin m, E m := by
      apply Finset.sum_le_sum
      intro i _
      exact box_coordinate_moment m L i
    _ = _ := by simp

private def cumulativeMass (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), Wsize k
private lemma cumulative_sum (n : ℕ) :
    (∑ p : cumulativePartition n, 1 / (supernorm p.2 : ℝ)) = cumulativeMass n := by
  simpa only [Fintype.sum_sigma, Wsize, cumulativeMass] using
    (Fin.sum_univ_eq_sum_range Wsize (n + 1))
private lemma low_box_mass_le (m L n : ℕ) :
    (∑ x ∈ (occupationBox m L).filter (fun x => energy (occupation m x) ≤ n),
      occupationWeight m x) ≤ cumulativeMass n := by
  classical
  let s := (occupationBox m L).filter (fun x => energy (occupation m x) ≤ n)
  let f : s → cumulativePartition n := fun x =>
    goodOccupationToPartition ⟨x.1, (mem_filter.mp x.2).2⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x : Fin m → ℕ // energy (occupation m x) ≤ n} => z.val)
      (goodOccupationToPartition_injective m n h)
  rw [← cumulative_sum]
  change (∑ x ∈ s, occupationWeight m x) ≤ _
  rw [← Finset.sum_coe_sort s (occupationWeight m)]
  apply Finset.sum_le_sum_of_injOn f hinj.injOn (Finset.subset_univ _)
  · intro x _
    exact (occupationWeight_eq m x.1).le
  · intro p _ _
    positivity
private lemma cumulative_lower (m n : ℕ) (hn : 0 < n) :
    E m * (1 - (m : ℝ) / n) ≤ cumulativeMass n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb (L : ℕ) :
      (∑ x ∈ occupationBox m L, occupationWeight m x) - (m : ℝ) * E m / n ≤
        cumulativeMass n := by
    have hm := box_moment_bound m L
    have hM := finite_markov (occupationBox m L) (occupationWeight m)
      (fun x => energy (occupation m x)) hn
      (fun x _ => occupationWeight_nonneg m x)
    have hlow := low_box_mass_le m L n
    have hdiv := div_le_div_of_nonneg_right hm hnR.le
    linarith
  have ht := (box_mass_limit m).sub_const ((m : ℝ) * E m / n)
  rw [← E_eq_fin m] at ht
  have h := le_of_tendsto ht (Filter.Eventually.of_forall hb)
  calc
    _ = E m - (m : ℝ) * E m / n := by ring
    _ ≤ _ := h
private def partitionCoordinates {n : ℕ} (p : cumulativePartition n) : Fin n → ℕ :=
  fun i => p.2.parts.count (i.val + 1)
private lemma partitionCoordinates_mem_box {n : ℕ} (p : cumulativePartition n) :
    partitionCoordinates p ∈ occupationBox n (n + 1) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply mem_range.mpr
  have hb := multiplicity_size_bound p.2 (i.val + 1)
  have hn := p.1.isLt
  dsimp [partitionCoordinates]
  nlinarith
private lemma partitionCoordinates_injective (n : ℕ) :
    Function.Injective (@partitionCoordinates n) := by
  intro p q h
  have hp : p.2.parts = q.2.parts := by
    apply Multiset.ext.mpr
    intro d
    by_cases hd : d ∈ Icc 1 n
    · obtain ⟨hd1, hdn⟩ := mem_Icc.mp hd
      have he := congrFun h ⟨d - 1, by omega⟩
      simpa [partitionCoordinates, Nat.sub_add_cancel hd1] using he
    · have hz (r : cumulativePartition n) : r.2.parts.count d = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hm
        exact hd (mem_Icc.mpr ⟨r.2.parts_pos hm,
          (r.2.le_of_mem_parts hm).trans (by have := r.1.isLt; omega)⟩)
      rw [hz p, hz q]
  rcases p with ⟨k, p⟩
  rcases q with ⟨l, q⟩
  have hkl : k = l := by
    apply Fin.ext
    simpa only [p.parts_sum, q.parts_sum] using congrArg Multiset.sum hp
  subst l
  have hpq : p = q := Nat.Partition.ext hp
  subst q
  rfl
private lemma partitionCoordinates_weight {n : ℕ} (p : cumulativePartition n) :
    occupationWeight n (partitionCoordinates p) = 1 / (supernorm p.2 : ℝ) := by
  classical
  have hp : p.2.parts.toFinset ⊆ Icc 1 n := by
    intro d hd
    have hm := Multiset.mem_toFinset.mp hd
    exact mem_Icc.mpr ⟨p.2.parts_pos hm,
      (p.2.le_of_mem_parts hm).trans (by have := p.1.isLt; omega)⟩
  have he : supernorm p.2 = ∏ i : Fin n,
      partPrime (i.val + 1) ^ p.2.parts.count (i.val + 1) := by
    calc
      _ = ∏ d ∈ Icc 1 n, partPrime d ^ p.2.parts.count d := by
        change (p.2.parts.map partPrime).prod = _
        rw [prod_multiset_map_count]
        apply prod_subset hp
        intro d _ hd
        rw [Multiset.count_eq_zero.mpr (fun hm => hd (Multiset.mem_toFinset.mpr hm)),
          pow_zero]
      _ = _ := by
        rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
        simpa [Nat.add_comm] using (Finset.prod_range (fun d : ℕ =>
          partPrime (d + 1) ^ p.2.parts.count (d + 1)))
  rw [he]
  simp only [occupationWeight, partitionCoordinates, Nat.cast_prod, Nat.cast_pow,
    one_div, Finset.prod_inv_distrib, inv_pow]
private lemma cumulative_upper (n : ℕ) : cumulativeMass n ≤ E n := by
  classical
  calc
    _ = ∑ p : cumulativePartition n, 1 / (supernorm p.2 : ℝ) :=
      (cumulative_sum n).symm
    _ ≤ ∑ x ∈ occupationBox n (n + 1), occupationWeight n x := by
      apply Finset.sum_le_sum_of_injOn partitionCoordinates
        (partitionCoordinates_injective n).injOn
      · intro x hx
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
        exact partitionCoordinates_mem_box p
      · intro p _
        exact (partitionCoordinates_weight p).symm.le
      · intro x _ _
        exact occupationWeight_nonneg n x
    _ = ∏ i : Fin n, ∑ r ∈ range (n + 1),
        (partPrime (i.val + 1) : ℝ)⁻¹ ^ r := box_mass_product n (n + 1)
    _ ≤ ∏ i : Fin n, (1 - (partPrime (i.val + 1) : ℝ)⁻¹)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      · intro i _
        exact geometric_partial (i.val + 1) (n + 1)
    _ = E n := (E_eq_fin n).symm
private lemma marked_part_reindex (n d : ℕ) (hd : 0 < d) :
    (∑ r ∈ Icc 1 (n / d),
      (d : ℝ) / (partPrime d : ℝ) ^ r * Wsize (n - r * d)) =
      ∑ j ∈ Icc 1 n, if d ∣ j then
        (d : ℝ) / (partPrime d : ℝ) ^ (j / d) * Wsize (n - j) else 0 := by
  rw [← sum_filter]
  apply sum_bij (fun r _ => r * d)
  · intro r hr
    obtain ⟨hr1, hrn⟩ := mem_Icc.mp hr
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,
      (Nat.le_div_iff_mul_le hd).mp hrn⟩, dvd_mul_left d r⟩
  · intro r hr s hs hrs
    exact Nat.eq_of_mul_eq_mul_right hd hrs
  · intro j hj
    obtain ⟨hj, hdj⟩ := mem_filter.mp hj
    obtain ⟨hj1, hjn⟩ := mem_Icc.mp hj
    refine ⟨j / d, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hjn⟩,
      Nat.div_mul_cancel hdj⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdj) hd
  · intro r hr
    simp [Nat.mul_div_cancel _ hd]
private lemma convolution_recurrence {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Wsize n = ∑ j ∈ Icc 1 n, b j * Wsize (n - j) := by
  rw [marked_part_recurrence]
  trans ∑ d ∈ Icc 1 n, ∑ j ∈ Icc 1 n, if d ∣ j then
    (d : ℝ) / (partPrime d : ℝ) ^ (j / d) * Wsize (n - j) else 0
  · apply sum_congr rfl
    intro d hd
    exact marked_part_reindex n d (mem_Icc.mp hd).1
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have hj1 : 0 < j := (mem_Icc.mp hj).1
  rw [b, sum_mul]
  rw [← sum_filter]
  apply sum_congr
  · ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, _⟩, hdj⟩
      exact ⟨hdj, by omega⟩
    · rintro ⟨hdj, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdj hj1,
        (Nat.le_of_dvd hj1 hdj).trans (mem_Icc.mp hj).2⟩, hdj⟩
  · intro d hd
    rfl
private lemma cumulative_limit :
    Tendsto (fun n : ℕ => cumulativeMass n / log n) atTop
      (𝓝 (exp eulerMascheroniConstant)) := by
  have hlo := ((E_log_limit.comp cutoff_top).mul cutoff_log_ratio).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub cutoff_small)
  simp only [mul_one, sub_zero, Function.comp_apply] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo E_log_limit
  · filter_upwards [eventually_ge_atTop 2, cutoff_top.eventually_ge_atTop 2]
      with n hn hm
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hm1 : (1 : ℝ) < cutoff n := by exact_mod_cast (by omega : 1 < cutoff n)
    have he : E (cutoff n) / log (cutoff n) * (log (cutoff n) / log n) *
        (1 - (cutoff n : ℝ) / n) =
        E (cutoff n) * (1 - (cutoff n : ℝ) / n) / log n := by
      field_simp [(log_pos hm1).ne']
    rw [he]
    exact div_le_div_of_nonneg_right
      (cumulative_lower (cutoff n) n (by omega)) (log_pos hn1).le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_le_div_of_nonneg_right (cumulative_upper n)
      (log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))

private lemma b_nonneg (n : ℕ) : 0 ≤ b n :=
  sum_nonneg fun _ _ => by positivity
private def convolutionTail (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (n / 2), b j * a (n - j)
private lemma kernel_half_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ, 0 < j → n ≤ 2 * j → j ≤ n → |b j * log n - 1| < ε := by
  intro ε hε
  let e : ℝ := min ε 1
  have he : 0 < e := lt_min hε zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hlo : ∀ᶠ j : ℕ in atTop, 1 - e / 4 < b j * log j :=
    kernel_log_limit.eventually (lt_mem_nhds (by linarith))
  have hhi : ∀ᶠ j : ℕ in atTop, b j * log j < 1 + e / 4 :=
    kernel_log_limit.eventually (gt_mem_nhds (by linarith))
  have hL : ∀ᶠ j : ℕ in atTop, 4 * log 2 / e < log j :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop _)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlo.and hhi).and hL)
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn
  intro j hj hnj hjn
  have hjN : N ≤ j := by omega
  obtain ⟨⟨hlo, hhi⟩, hL⟩ := hN j hjN
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hnr : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hj hjn)
  have hlogle : log j ≤ log n := log_le_log hjr (by exact_mod_cast hjn)
  have hlogupper : log n ≤ log 2 + log j := by
    calc
      _ ≤ log (2 * (j : ℝ)) := log_le_log hnr (by exact_mod_cast hnj)
      _ = _ := log_mul (by norm_num) hjr.ne'
  have hbL : b j * log j < 2 := by linarith
  have hLb : 4 * log 2 < e * log j := by
    simpa only [mul_comm] using (div_lt_iff₀ he).mp hL
  have hbil : b j * log 2 < e / 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hLb.le (b_nonneg j)
    have h₂ := mul_lt_mul_of_pos_left hbL he
    nlinarith
  have hlow := mul_le_mul_of_nonneg_left hlogle (b_nonneg j)
  have hupp := mul_le_mul_of_nonneg_left hlogupper (b_nonneg j)
  have habs : |b j * log n - 1| < e := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  exact habs.trans_le heε
private lemma kernel_cesaro_small :
    Tendsto (fun n : ℕ => (∑ j ∈ Icc 1 (n / 2), b j) / (n : ℝ))
      atTop (𝓝 0) := by
  have hb0 : Tendsto b atTop (𝓝 0) := by
    have h := kernel_log_limit.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact mul_div_cancel_right₀ (b n) (log_pos hn1).ne'
  have hc := hb0.cesaro
  apply squeeze_zero'
    (Eventually.of_forall fun n => div_nonneg (sum_nonneg fun j _ => b_nonneg j)
      (Nat.cast_nonneg n))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hs : (∑ j ∈ Icc 1 (n / 2), b j) ≤ ∑ j ∈ range n, b j := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have hj2 := (mem_Icc.mp hj).2
        exact mem_range.mpr (by omega)
      · intro j _ _
        exact b_nonneg j
    simpa only [div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
  · simpa only [mul_comm] using hc
private def convolutionFront (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n - n / 2), b (n - k) * a k
private lemma convolution_split (n : ℕ) :
    (∑ j ∈ Icc 1 n, b j * Wsize (n - j)) =
      convolutionFront Wsize b n + convolutionTail Wsize b n := by
  have hr : (∑ j ∈ Ico (n / 2 + 1) (n + 1), b j * Wsize (n - j)) =
      convolutionFront Wsize b n := by
    calc
      _ = ∑ j ∈ Ico (n / 2 + 1) (n + 1),
          (fun k => b (n - k) * Wsize k) (n - j) := by
        apply sum_congr rfl
        intro j hj
        have hjn : j ≤ n := by have := (mem_Ico.mp hj).2; omega
        dsimp only
        rw [Nat.sub_sub_self hjn]
      _ = ∑ k ∈ Ico (n + 1 - (n + 1)) (n + 1 - (n / 2 + 1)),
          b (n - k) * Wsize k :=
        sum_Ico_reflect (fun k => b (n - k) * Wsize k) (n / 2 + 1) (by omega)
      _ = convolutionFront Wsize b n := by
        simp only [Nat.sub_self, Nat.add_sub_add_right, Nat.Ico_zero_eq_range,
          convolutionFront]
  have hs := sum_Ico_consecutive (fun j => b j * Wsize (n - j))
    (show 1 ≤ n / 2 + 1 by omega) (show n / 2 + 1 ≤ n + 1 by omega)
  rw [hr] at hs
  simpa only [Ico_add_one_right_eq_Icc, convolutionTail] using hs.symm.trans
    (add_comm _ _)
private lemma half_cumulative_limit :
    Tendsto (fun n : ℕ => (∑ k ∈ range (n - n / 2), Wsize k) / log n)
      atTop (𝓝 (exp eulerMascheroniConstant)) := by
  let r : ℕ → ℕ := fun n => n - n / 2 - 1
  have hr : Tendsto r atTop atTop := by
    convert (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_sub_atTop_nat 1) using 1
    ext n
    dsimp [r]
    omega
  have hratio : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop (𝓝 (1 / 2)) := by
    have h := ((tendsto_const_nhds (x := (1 / 2 : ℝ))).add
      ((tendsto_mod_div_atTop_nhds_zero_nat (m := 2) (by norm_num)).div_const 2)).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    norm_num only [zero_div, add_zero, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have he : n + n % 2 = 2 * r n + 2 := by dsimp [r]; omega
    have heR : (n : ℝ) + (n % 2 : ℕ) = 2 * (r n : ℝ) + 2 := by exact_mod_cast he
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp [hn0]
    nlinarith
  have hlogn := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogratio : Tendsto (fun n : ℕ => log (r n) / log n) atTop (𝓝 1) := by
    have h := ((hratio.log (by norm_num : (1 / 2 : ℝ) ≠ 0)).div_atTop hlogn).add_const 1
    norm_num only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2, hr.eventually_gt_atTop 0] with n hn hr0
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    dsimp only [Function.comp_apply] at h ⊢
    rw [log_div (by positivity : (r n : ℝ) ≠ 0) (by positivity : (n : ℝ) ≠ 0),
      sub_div, div_self (log_pos hn1).ne']
    ring
  have h := (cumulative_limit.comp hr).mul hlogratio
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 8] with n hn
  have hr1 : (1 : ℝ) < r n := by
    exact_mod_cast (show 1 < r n by dsimp [r]; omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have heq : r n + 1 = n - n / 2 := by dsimp [r]; omega
  dsimp only [Function.comp_def, cumulativeMass]
  rw [heq]
  field_simp [(log_pos hr1).ne', (log_pos hn1).ne']
private lemma convolution_front_limit :
    Tendsto (convolutionFront Wsize b) atTop (𝓝 (exp eulerMascheroniConstant)) := by
  have hpart := half_cumulative_limit
  let mass : ℕ → ℝ := fun n => (∑ k ∈ range (n - n / 2), Wsize k) / log n
  have herr : (fun n => convolutionFront Wsize b n - mass n) =o[atTop] mass := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    filter_upwards [kernel_half_uniform ε hε, eventually_ge_atTop 2]
      with n hw hn
    have hl : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < n))
    have heq : convolutionFront Wsize b n - mass n =
        ∑ k ∈ range (n - n / 2),
          (b (n - k) * log n - 1) * (Wsize k / log n) := by
      dsimp [convolutionFront, mass]
      rw [sum_div, ← sum_sub_distrib]
      apply sum_congr rfl
      intro k _
      field_simp [hl.ne']
    rw [Real.norm_eq_abs, heq, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sum_nonneg fun k _ => Wsize_nonneg k) hl.le)]
    calc
      _ ≤ ∑ k ∈ range (n - n / 2),
          |(b (n - k) * log n - 1) * (Wsize k / log n)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range (n - n / 2), ε * (Wsize k / log n) := by
        apply sum_le_sum
        intro k hk
        have hk' := mem_range.mp hk
        rw [abs_mul, abs_of_nonneg (div_nonneg (Wsize_nonneg k) hl.le)]
        exact mul_le_mul_of_nonneg_right (hw (n - k) (by omega) (by omega)
          (by omega)).le (div_nonneg (Wsize_nonneg k) hl.le)
      _ = ε * mass n := by dsimp [mass]; rw [sum_div, mul_sum]
  simpa only [mass, sub_add_cancel, zero_add] using
    (herr.tendsto_zero_of_tendsto hpart).add hpart
private lemma convolution_tail_bound (K : ℝ) (n : ℕ) (hn : 0 < n)
    (hK : ∀ k : ℕ, 0 < k → k < n → (k : ℝ) * Wsize k ≤ K) :
    convolutionTail Wsize b n ≤
      2 * K * ((∑ j ∈ Icc 1 (n / 2), b j) / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ ∑ j ∈ Icc 1 (n / 2), b j * (2 * K / (n : ℝ)) := by
      apply sum_le_sum
      intro j hj
      obtain ⟨hj1, hj2⟩ := mem_Icc.mp hj
      apply mul_le_mul_of_nonneg_left _ (b_nonneg j)
      apply (le_div_iff₀ hn0).mpr
      have hbound := hK (n - j) (by omega) (by omega)
      have hcast : (n : ℝ) ≤ 2 * (n - j : ℕ) := by
        exact_mod_cast (show n ≤ 2 * (n - j) by omega)
      nlinarith [mul_le_mul_of_nonneg_left hcast (Wsize_nonneg (n - j))]
    _ = _ := by rw [← sum_mul]; ring

/-- The fixed-size reciprocal supernorm sum has leading term `exp γ / n`. -/
theorem result :
    Tendsto (fun n : ℕ => (n : ℝ) * Wsize n) atTop
      (𝓝 (exp eulerMascheroniConstant)) := by
  classical
  let C : ℝ := exp eulerMascheroniConstant
  have hfront := convolution_front_limit
  have hsmall := kernel_cesaro_small
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hfront.eventually (gt_mem_nhds (lt_add_one C))).and
      (hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))))
  let S : ℝ := ∑ k ∈ range N, (k : ℝ) * Wsize k
  let K : ℝ := 2 * max (C + 1) 0 + S
  have hS : 0 ≤ S := sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (Wsize_nonneg k)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKD : 2 * (C + 1) ≤ K := by
    dsimp [K]
    linarith [le_max_left (C + 1) 0]
  have hK : ∀ n : ℕ, 0 < n → (n : ℝ) * Wsize n ≤ K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hlt : n < N
      · have hs : (n : ℝ) * Wsize n ≤ S :=
          single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg k) (Wsize_nonneg k))
            (mem_range.mpr hlt)
        dsimp [K]
        linarith [le_max_right (C + 1) 0]
      · have ht := convolution_tail_bound K n hn
          (fun k hk hkn => ih k hkn hk)
        have hlarge := hN n (by omega)
        rw [convolution_recurrence hn, convolution_split n]
        have : convolutionTail Wsize b n ≤ K / 2 := by nlinarith [hlarge.2]
        linarith [hlarge.1]
  have htail : Tendsto (convolutionTail Wsize b) atTop (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n => sum_nonneg fun j _ =>
        mul_nonneg (b_nonneg j) (Wsize_nonneg (n - j)))
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact convolution_tail_bound K n hn (fun k hk _ => hK k hk)
    · simpa using hsmall.const_mul (2 * K)
  have h := hfront.add htail
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact ((convolution_recurrence hn).trans (convolution_split n)).symm

end D5.S3.Arith.Partitions.SupernormSizeAsymptotic
