/- GID: D5/S3/Arith/Robin/EulerLayerInventoryGrowth
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayerInventoryGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict Euler inventories have uniform square-root discrepancy from Chebyshev psi. -/

import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import D5.S3.Arith.GoldenLayerMarginalDecay
import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace D5.S3.Arith.Robin.EulerLayerInventoryGrowth

open Finset Filter Asymptotics
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenLayerMarginalDecay
open scoped Topology Chebyshev

noncomputable section

/-- The logarithm splits into the first prime layer and the naturally truncated
mass of all remaining layers. The subtraction is used only on occupied support. -/
theorem log_factorization_split {U : ℕ} (hU : 0 < U) :
    Real.log U = (∑ q ∈ U.primeFactors, Real.log q) +
      ∑ q ∈ U.primeFactors, ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have ha : 1 ≤ U.factorization q :=
    (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hq)
  rw [Nat.cast_sub ha]
  ring

/-- Positive divisibility increases the full higher-layer mass. Missing primes
contribute zero through natural truncated subtraction. -/
theorem higher_layer_mass_mono {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hAB : A ∣ B) :
    (∑ p ∈ A.primeFactors, ((A.factorization p - 1 : ℕ) : ℝ) * Real.log p) ≤
      ∑ p ∈ B.primeFactors, ((B.factorization p - 1 : ℕ) : ℝ) * Real.log p := by
  have hval := (Nat.factorization_le_iff_dvd hA.ne' hB.ne').mpr hAB
  calc
    _ ≤ ∑ p ∈ A.primeFactors, ((B.factorization p - 1 : ℕ) : ℝ) * Real.log p := by
      apply sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le_sub_right (hval p) 1) (Real.log_natCast_nonneg p)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hAB hB.ne')
      (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))

private theorem layer_active {t : ℝ} (ht : 1 < t) {U q k : ℕ}
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q)
    (hq : q.Prime) (hk : 1 ≤ k) (hka : k ≤ U.factorization q) :
    1 / (t * Real.log t) < goldenLayerMarginal q k := by
  have hprice : 0 < 1 / (t * Real.log t) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ht))
  have hmem : k ∈ Set.Icc 1 (optimalLayerCount (1 / (t * Real.log t)) q) :=
    ⟨hk, by rwa [← hstrict q hq]⟩
  rw [← positive_layers_eq_count_interval hprice hq] at hmem
  exact hmem.2.2

theorem active_power_bound {t : ℝ} (ht : 1 < t) {U q k : ℕ}
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q)
    (hq : q.Prime) (hk : 1 ≤ k) (hka : k ≤ U.factorization q) :
    (q : ℝ) ^ k * Real.log q < t * Real.log t := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hgain := (layer_active ht hstrict hq hk hka).trans_le
    (golden_layer_marginal_le_inv_pow hq hk)
  have heq : (q : ℝ)⁻¹ ^ k / Real.log q =
      1 / ((q : ℝ) ^ k * Real.log q) := by simp [inv_pow, div_eq_mul_inv, mul_comm]
  rw [heq, div_lt_div_iff₀ (mul_pos (by linarith) (Real.log_pos ht))
    (mul_pos (pow_pos hq0 _) hlq)] at hgain
  simpa using hgain

private theorem support_bounds {t : ℝ} (ht : 1 < t) {U : ℕ} (hU : 0 < U)
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) :
    (∀ q ∈ U.primeFactors, (q : ℝ) < t) ∧
    (∀ q : ℕ, q.Prime → (q : ℝ) + 1 ≤ t → q ∈ U.primeFactors) := by
  have ht0 : 0 < t := by linarith
  constructor
  · intro q hqU
    have hq := Nat.prime_of_mem_primeFactors hqU
    have hqa : 1 ≤ U.factorization q :=
      hq.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hqU)
    have hbound := active_power_bound ht hstrict hq (k := 1) le_rfl hqa
    simp only [pow_one] at hbound
    by_contra h
    have htq : t ≤ (q : ℝ) := le_of_not_gt h
    have hmul : t * Real.log t ≤ (q : ℝ) * Real.log q :=
      mul_le_mul htq (Real.log_le_log ht0 htq) (Real.log_pos ht).le
        (by exact_mod_cast hq.pos.le)
    linarith
  · intro q hq hqt
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hlq := Real.log_pos (by exact_mod_cast hq.one_lt : (1 : ℝ) < q)
    have hlog : 1 / ((q : ℝ) + 1) ≤ Real.log (1 + 1 / (q : ℝ)) := by
      convert Real.one_sub_inv_le_log_of_pos
        (show 0 < 1 + 1 / (q : ℝ) by positivity) using 1
      field_simp
      <;> ring
    have hmul : ((q : ℝ) + 1) * Real.log q < t * Real.log t := calc
      _ < ((q : ℝ) + 1) * Real.log ((q : ℝ) + 1) :=
        mul_lt_mul_of_pos_left (Real.log_lt_log hq0 (by linarith)) (by positivity)
      _ ≤ t * Real.log t :=
        mul_le_mul hqt (Real.log_le_log (by positivity) hqt)
          (Real.log_nonneg (by linarith)) ht0.le
    have hgain : 1 / (t * Real.log t) < goldenLayerMarginal q 1 := by
      rw [golden_layer_marginal_one_eq_log_one_add_inv hq]
      calc
        _ < 1 / (((q : ℝ) + 1) * Real.log q) :=
          one_div_lt_one_div_of_lt (mul_pos (by positivity) hlq) hmul
        _ = (1 / ((q : ℝ) + 1)) / Real.log q := by simp [div_eq_mul_inv, mul_comm]
        _ ≤ _ := div_le_div_of_nonneg_right hlog hlq.le
    have hprice := one_div_pos.mpr (mul_pos ht0 (Real.log_pos ht))
    have hmem : 1 ∈ Set.Icc 1 (optimalLayerCount (1 / (t * Real.log t)) q) := by
      rw [← positive_layers_eq_count_interval hprice hq]
      exact ⟨le_rfl, hq, hgain⟩
    apply hq.mem_primeFactors
    · apply (hq.dvd_iff_one_le_factorization (by omega)).mpr
      rw [hstrict q hq]
      exact hmem.2
    · omega

theorem first_layer_comparison {t : ℝ} (ht : 2 ≤ t) {U : ℕ} (hU : 0 < U)
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) :
    θ t - Real.log t ≤ ∑ q ∈ U.primeFactors, Real.log q ∧
      (∑ q ∈ U.primeFactors, Real.log q) ≤ θ t := by
  classical
  obtain ⟨hupper, hlower⟩ := support_bounds (by linarith) hU hstrict
  let P := Nat.primesLE ⌊t⌋₊
  have hsub : U.primeFactors ⊆ P := by
    intro q hq
    exact Nat.mem_primesLE.mpr ⟨
      (Nat.le_floor_iff (by linarith : 0 ≤ t)).mpr (hupper q hq).le,
      Nat.prime_of_mem_primeFactors hq⟩
  have hmissing : P \ U.primeFactors ⊆ {⌊t⌋₊} := by
    intro q hq
    obtain ⟨hqP, hqU⟩ := mem_sdiff.mp hq
    obtain ⟨hqt, hq⟩ := Nat.mem_primesLE.mp hqP
    have hleft : t < (q : ℝ) + 1 := by
      by_contra h
      exact hqU (hlower q hq (le_of_not_gt h))
    have hfq : ⌊t⌋₊ ≤ q := by
      have hh : ⌊t⌋₊ < q + 1 := (Nat.floor_lt (by linarith : 0 ≤ t)).mpr
        (by simpa only [Nat.cast_add, Nat.cast_one] using hleft)
      omega
    simpa using le_antisymm hqt hfq
  have hdeficit : (∑ q ∈ P \ U.primeFactors, Real.log q) ≤ Real.log t := calc
    _ ≤ ∑ q ∈ ({⌊t⌋₊} : Finset ℕ), Real.log q :=
      sum_le_sum_of_subset_of_nonneg hmissing (fun q _ _ => Real.log_natCast_nonneg q)
    _ = Real.log (⌊t⌋₊ : ℝ) := by simp
    _ ≤ Real.log t := Real.log_le_log
      (by exact_mod_cast (show 0 < ⌊t⌋₊ by
        have hh : (2 : ℕ) ≤ ⌊t⌋₊ :=
          (Nat.le_floor_iff (by linarith : 0 ≤ t)).mpr ht
        omega)) (Nat.floor_le (by linarith))
  have hpartition := sum_sdiff hsub (f := fun q : ℕ => Real.log q)
  rw [Chebyshev.theta_eq_sum_primesLE]
  change (∑ q ∈ P, Real.log q) - Real.log t ≤ _ ∧ _ ≤ ∑ q ∈ P, Real.log q
  refine ⟨by linarith, sum_le_sum_of_subset_of_nonneg hsub ?_⟩
  exact fun q _ _ => Real.log_natCast_nonneg q

private theorem higher_layer_comparison {t : ℝ} (ht : 2 ≤ t) {U : ℕ} (hU : 0 < U)
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) :
    (∑ q ∈ U.primeFactors, ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q) ≤
      ψ (t * Real.log t / Real.log 2) - θ (t * Real.log t / Real.log 2) := by
  classical
  let Y := t * Real.log t / Real.log 2
  let M := ⌊Y⌋₊
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact (div_pos (mul_pos (by linarith) (Real.log_pos (by linarith))) hl2).le
  have hval (q : ℕ) (hqU : q ∈ U.primeFactors) : U.factorization q ≤ Nat.log q M := by
    have hq := Nat.prime_of_mem_primeFactors hqU
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hqa : 1 ≤ U.factorization q :=
      hq.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hqU)
    have hb := active_power_bound (by linarith) hstrict hq hqa le_rfl
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast hq.two_le : (2 : ℝ) ≤ q)
    have hpow : (q : ℝ) ^ U.factorization q < Y := by
      apply (lt_div_iff₀ hl2).mpr
      exact (mul_le_mul_of_nonneg_left hl (pow_pos hq0 _).le).trans_lt hb
    apply Nat.le_log_of_pow_le hq.one_lt
    apply (Nat.le_floor_iff hY).mpr
    exact_mod_cast hpow.le
  have hsub : U.primeFactors ⊆ Nat.primesLE M := by
    intro q hqU
    have hq := Nat.prime_of_mem_primeFactors hqU
    refine Nat.mem_primesLE.mpr ⟨?_, hq⟩
    have hqa : 1 ≤ U.factorization q :=
      hq.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hqU)
    have hlog : 0 < Nat.log q M := hqa.trans (hval q hqU)
    have hM : M ≠ 0 := by intro hz; simp [hz] at hlog
    simpa only [pow_one] using Nat.pow_le_of_le_log hM (hqa.trans (hval q hqU))
  have hcast (q : ℕ) (hq : q ∈ Nat.primesLE M) :
      ((Nat.log q M - 1 : ℕ) : ℝ) = (Nat.log q M : ℝ) - 1 := by
    obtain ⟨hqM, hqprime⟩ := Nat.mem_primesLE.mp hq
    simpa only [Nat.cast_one] using Nat.cast_sub (Nat.log_pos hqprime.one_lt hqM)
  calc
    _ ≤ ∑ q ∈ U.primeFactors, ((Nat.log q M - 1 : ℕ) : ℝ) * Real.log q := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right (hval q hq) 1)
        (Real.log_natCast_nonneg q)
    _ ≤ ∑ q ∈ Nat.primesLE M, ((Nat.log q M - 1 : ℕ) : ℝ) * Real.log q :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ = ψ (M : ℝ) - θ (M : ℝ) := by
      rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log,
        ← sum_sub_distrib]
      apply sum_congr rfl
      intro q hq
      rw [hcast q hq]
      ring
    _ = _ := by
      rw [Chebyshev.psi_eq_psi_coe_floor Y, Chebyshev.theta_eq_theta_coe_floor Y]

/-- The actual strict integer lies between the first-prime mass less one boundary weight
and the first-prime mass plus the complete higher prime-power reference mass. -/
theorem strict_inventory_chebyshev_bounds {t : ℝ} (ht : 2 ≤ t) {U : ℕ} (hU : 0 < U)
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) :
    θ t - Real.log t ≤ Real.log U ∧
      Real.log U ≤ θ t + ψ (t * Real.log t / Real.log 2) -
        θ (t * Real.log t / Real.log 2) := by
  have hfirst := first_layer_comparison ht hU hstrict
  have hhigher := higher_layer_comparison ht hU hstrict
  have hsplit := log_factorization_split hU
  have hnonneg : 0 ≤ ∑ q ∈ U.primeFactors,
      ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q :=
    sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q)
  constructor <;> linarith

#print axioms strict_inventory_chebyshev_bounds

theorem active_power_linear_cutoff {t : ℝ} (ht : 2 ≤ t) {U q k : ℕ}
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q)
    (hq : q.Prime) (hk : 1 ≤ k) (hka : k ≤ U.factorization q) :
    (q : ℝ) ^ k < (k : ℝ) * t := by
  have ht0 : 0 < t := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbound := active_power_bound (by linarith) hstrict hq hk hka
  by_contra hn
  have hpow : (k : ℝ) * t ≤ (q : ℝ) ^ k := le_of_not_gt hn
  have htx : t ≤ (q : ℝ) ^ k := calc
    _ = 1 * t := by ring
    _ ≤ (k : ℝ) * t := mul_le_mul_of_nonneg_right hk1 ht0.le
    _ ≤ _ := hpow
  have hlog : Real.log t ≤ (k : ℝ) * Real.log q := by
    simpa only [Real.log_pow] using Real.log_le_log ht0 htx
  have hreverse : t * Real.log t ≤ (q : ℝ) ^ k * Real.log q := calc
    _ ≤ t * ((k : ℝ) * Real.log q) := mul_le_mul_of_nonneg_left hlog ht0.le
    _ = ((k : ℝ) * t) * Real.log q := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.log_natCast_nonneg q)
  linarith

/-- The complete actual higher-layer mass has a finite square-root-scale envelope at
the same real clock. Every actual valuation and the literal strict tie convention remain. -/
theorem strict_inventory_higher_layer_bound {t : ℝ} (ht : 2 ≤ t) {U : ℕ} (hU : 0 < U)
    (hstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) :
    (∑ q ∈ U.primeFactors, ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q) ≤
      2 * θ (Real.sqrt (2 * t)) + 2 * (ψ t - θ t) := by
  classical
  let S := U.primeFactors.filter (fun q => 2 ≤ U.factorization q)
  let M := ⌊t⌋₊
  have ht0 : 0 < t := by linarith
  have hSU : S ⊆ U.primeFactors := filter_subset _ _
  have hsupport := (support_bounds (by linarith) hU hstrict).1
  have hsub : S ⊆ Nat.primesLE M := by
    intro q hqS
    exact Nat.mem_primesLE.mpr ⟨
      (Nat.le_floor_iff ht0.le).mpr (hsupport q (hSU hqS)).le,
      Nat.prime_of_mem_primeFactors (hSU hqS)⟩
  have hval (q : ℕ) (hqS : q ∈ S) :
      U.factorization q - 1 ≤ 2 * Nat.log q M := by
    have hq := Nat.prime_of_mem_primeFactors (hSU hqS)
    have hqa : 2 ≤ U.factorization q := (mem_filter.mp hqS).2
    let k := U.factorization q / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hka : 2 * k ≤ U.factorization q := by dsimp [k]; omega
    have hactive := active_power_linear_cutoff ht hstrict hq (by omega : 1 ≤ 2 * k) hka
    have hpoweq : (q : ℝ) ^ (2 * k) = ((q : ℝ) ^ k) ^ 2 := by
      rw [Nat.mul_comm 2 k, pow_mul]
    rw [hpoweq] at hactive
    have hcoeff : (2 * k : ℕ) ≤ q ^ k :=
      (Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) k).trans
        (Nat.pow_le_pow_left hq.two_le k)
    have hcoeffR : ((2 * k : ℕ) : ℝ) ≤ (q : ℝ) ^ k := by exact_mod_cast hcoeff
    have hcoeff0 : 0 ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hqpow : (q : ℝ) ^ k < t := by
      by_contra hn
      have htx : t ≤ (q : ℝ) ^ k := le_of_not_gt hn
      have hreverse : ((2 * k : ℕ) : ℝ) * t ≤ ((q : ℝ) ^ k) ^ 2 := calc
        _ ≤ ((2 * k : ℕ) : ℝ) * (q : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left htx hcoeff0
        _ ≤ (q : ℝ) ^ k * (q : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hcoeffR (pow_nonneg (Nat.cast_nonneg q) k)
        _ = _ := by ring
      linarith
    have hqpowNat : q ^ k ≤ M := by
      apply (Nat.le_floor_iff ht0.le).mpr
      exact_mod_cast hqpow.le
    have hklog : k ≤ Nat.log q M := Nat.le_log_of_pow_le hq.one_lt hqpowNat
    have hvalk : U.factorization q - 1 ≤ 2 * k := by dsimp [k]; omega
    exact hvalk.trans (Nat.mul_le_mul_left 2 hklog)
  have hsubroot : S ⊆ Nat.primesLE ⌊Real.sqrt (2 * t)⌋₊ := by
    intro q hqS
    have hq := Nat.prime_of_mem_primeFactors (hSU hqS)
    have hqa : 2 ≤ U.factorization q := (mem_filter.mp hqS).2
    have hpow := active_power_linear_cutoff ht hstrict hq (k := 2) (by norm_num) hqa
    have hpow' : (q : ℝ) ^ 2 < 2 * t := by simpa using hpow
    have hroot : (q : ℝ) < Real.sqrt (2 * t) :=
      (Real.lt_sqrt (Nat.cast_nonneg q)).mpr hpow'
    exact Nat.mem_primesLE.mpr ⟨
      (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr hroot.le, hq⟩
  have hcast (q : ℕ) (hq : q ∈ Nat.primesLE M) :
      ((Nat.log q M - 1 : ℕ) : ℝ) = (Nat.log q M : ℝ) - 1 := by
    obtain ⟨hqM, hqprime⟩ := Nat.mem_primesLE.mp hq
    simpa only [Nat.cast_one] using Nat.cast_sub (Nat.log_pos hqprime.one_lt hqM)
  have href :
      (∑ q ∈ Nat.primesLE M, ((Nat.log q M - 1 : ℕ) : ℝ) * Real.log q) =
        ψ t - θ t := calc
    _ = ψ (M : ℝ) - θ (M : ℝ) := by
      rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log,
        ← sum_sub_distrib]
      apply sum_congr rfl
      intro q hq
      rw [hcast q hq]
      ring
    _ = _ := by
      rw [Chebyshev.psi_eq_psi_coe_floor t, Chebyshev.theta_eq_theta_coe_floor t]
  have htail : (∑ q ∈ S, ((Nat.log q M - 1 : ℕ) : ℝ) * Real.log q) ≤ ψ t - θ t := by
    rw [← href]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
  have hfirst : (∑ q ∈ S, Real.log q) ≤ θ (Real.sqrt (2 * t)) := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact sum_le_sum_of_subset_of_nonneg hsubroot (fun q _ _ => Real.log_natCast_nonneg q)
  have hfilter :
      (∑ q ∈ U.primeFactors, ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q) =
        ∑ q ∈ S, ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q := by
    dsimp [S]
    rw [sum_filter]
    apply sum_congr rfl
    intro q hq
    by_cases hq2 : 2 ≤ U.factorization q
    · simp [hq2]
    · have hz : U.factorization q - 1 = 0 := by omega
      simp [hq2, hz]
  calc
    _ = ∑ q ∈ S, ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q := hfilter
    _ ≤ ∑ q ∈ S, 2 * (Nat.log q M : ℝ) * Real.log q := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hval q hq)
        (Real.log_natCast_nonneg q)
    _ = 2 * (∑ q ∈ S, ((Nat.log q M - 1 : ℕ) : ℝ) * Real.log q) +
        2 * (∑ q ∈ S, Real.log q) := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro q hq
      rw [hcast q (hsub hq)]
      ring
    _ ≤ _ := by linarith

#print axioms strict_inventory_higher_layer_bound

/-- A single positive constant bounds the discrepancy from the weak Chebyshev psi
function for every real clock at least two and every literal full strict inventory. -/
theorem strict_inventory_sqrt_discrepancy :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      |Real.log U - ψ t| ≤ C * Real.sqrt t := by
  obtain ⟨c, hc⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  let C : ℝ := 3 + 4 * Real.log 4 + |c|
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht U hU hstrict
  have ht0 : 0 ≤ t := by linarith
  have hfirst := first_layer_comparison ht hU hstrict
  have hhigher := strict_inventory_higher_layer_bound ht hU hstrict
  have hsplit := log_factorization_split hU
  have hnonneg : 0 ≤ ∑ q ∈ U.primeFactors,
      ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q :=
    sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q)
  have htail : ψ t - θ t ≤ |c| * Real.sqrt t :=
    (hc t).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (Real.sqrt_nonneg t))
  have hlog : Real.log t ≤ 2 * Real.sqrt t := by
    have h := Real.log_le_self (Real.sqrt_nonneg t)
    rw [Real.log_sqrt ht0] at h
    linarith
  have hroot : Real.sqrt (2 * t) ≤ 2 * Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt ht0]
  have htheta : θ (Real.sqrt (2 * t)) ≤ 2 * Real.log 4 * Real.sqrt t := calc
    _ ≤ Real.log 4 * Real.sqrt (2 * t) :=
      Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg _)
    _ ≤ Real.log 4 * (2 * Real.sqrt t) := mul_le_mul_of_nonneg_left hroot hlog4
    _ = _ := by ring
  have hlog4root : 0 ≤ Real.log 4 * Real.sqrt t :=
    mul_nonneg hlog4 (Real.sqrt_nonneg t)
  apply abs_le.mpr
  dsimp [C]
  constructor <;> nlinarith [Real.sqrt_nonneg t]

#print axioms strict_inventory_sqrt_discrepancy


/-- One threshold controls every positive natural integer satisfying the literal strict
prime-count law. No Riemann-hypothesis premise enters the conclusion. -/
theorem strict_inventory_uniform_growth :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
      (∀ q : ℕ, q.Prime →
        U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
      |Real.log U / t - 1| < ε := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  have hexp : Tendsto (fun t : ℝ => Real.exp (-c * Real.log t ^ (1 / 10 : ℝ)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hc)).mpr
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
        Real.tendsto_log_atTop))
  have hsmall : (fun t : ℝ => t * Real.exp (-c * Real.log t ^ (1 / 10 : ℝ)))
      =o[atTop] (fun t => t) := by
    simpa using (isBigO_refl (fun t : ℝ => t) atTop).mul_isLittleO
      ((isLittleO_one_iff ℝ).mpr hexp)
  have hpsi := (hpnt.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt t / t) atTop (𝓝 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  have hsqrto : Real.sqrt =o[atTop] (fun t : ℝ => t) :=
    isLittleO_of_tendsto (fun t ht => by simp [ht]) hsqrt
  have htail := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrto).tendsto_div_nhds_zero
  have htheta : Tendsto (fun t : ℝ => θ t / t - 1) atTop (𝓝 0) := by
    have h := hpsi.sub htail
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Pi.sub_apply, id_eq]
    field_simp
    <;> ring
  have hroot : Tendsto (fun t : ℝ => Real.sqrt (t * Real.log t / Real.log 2) / t)
      atTop (𝓝 0) := by
    have h := (hlog.div_const (Real.log 2)).sqrt
    simp only [zero_div, Real.sqrt_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have heq : Real.log t / t / Real.log 2 =
        (t * Real.log t / Real.log 2) / t ^ 2 := by field_simp
    rw [heq, Real.sqrt_div' _ (sq_nonneg t), Real.sqrt_sq ht.le]
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hCroot : Tendsto (fun t : ℝ => C * Real.sqrt (t * Real.log t / Real.log 2) / t)
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hroot.const_mul C
  intro ε hε
  have hθevent : ∀ᶠ t : ℝ in atTop, |θ t / t - 1| < ε / 3 := by
    have hθabs : Tendsto (fun t : ℝ => |θ t / t - 1|) atTop (𝓝 0) := by
      simpa only [abs_zero] using htheta.abs
    exact hθabs.eventually_lt_const (show (0 : ℝ) < ε / 3 by linarith)
  have hlevent := hlog.eventually_lt_const (show (0 : ℝ) < ε / 3 by linarith)
  have hrevent := hCroot.eventually_lt_const (show (0 : ℝ) < ε / 3 by linarith)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hθevent.and (hlevent.and hrevent))
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right T 2), ?_⟩
  intro t ht U hU hstrict
  have ht2 : 2 ≤ t := (le_max_right T 2).trans ht
  have ht0 : 0 < t := by linarith
  obtain ⟨hθ, hl, hr⟩ := hT t ((le_max_left T 2).trans ht)
  obtain ⟨hlower, hupper⟩ := strict_inventory_chebyshev_bounds ht2 hU hstrict
  have hupper' : Real.log U ≤ θ t + C * Real.sqrt (t * Real.log t / Real.log 2) := by
    linarith [hC (t * Real.log t / Real.log 2)]
  have hlo := (div_le_div_of_nonneg_right hlower ht0.le)
  have hup := (div_le_div_of_nonneg_right hupper' ht0.le)
  rw [sub_div] at hlo
  rw [add_div] at hup
  obtain ⟨hθlo, hθhi⟩ := abs_lt.mp hθ
  apply abs_lt.mpr
  constructor <;> linarith

#print axioms strict_inventory_uniform_growth

end
end D5.S3.Arith.Robin.EulerLayerInventoryGrowth
