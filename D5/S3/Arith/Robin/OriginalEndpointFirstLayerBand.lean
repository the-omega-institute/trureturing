/- GID: D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalEndpointFirstLayerBand
   mirror-E: none(waiver:general-analytic-results-no-numerical-evidence-artifact)
   anchors: []
   utility: none
   digest: Actual endpoint first-layer separation and complete same-integer Euler-tail lower bounds on the square-root logarithmic scale. -/

import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import D5.S3.Arith.GoldenLayerMarginalDecay
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
An omitted Bertrand prime bounds the price from below. A strict analytic
denominator gap excludes every second layer for primes in the actual support
band from twice the square root of its largest prime to that prime. A further
Bertrand prime gives a complete-tail lower bound of `1 / (16 * u)` for `u ≥ 16`.

The same first-layer band controls the difference of Chebyshev theta values.
Existing Chebyshev estimates give an explicit lower bound for `u ≥ 64`, and
elementary logarithm estimates give the positive lower bound
`log 2 / (32 * sqrt u * log (8 * sqrt u))` for `u ≥ 2 ^ 22`.

All positive prices, both original endpoints and every activation tie remain
in scope. Every prime and layer outside the chosen band remains in the same
integer's complete tail with a nonnegative contribution. The complete original
Robin residual still requires joint control of its remaining terms; no final
Robin sign or RH conclusion is asserted here.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenSmallestMissingPrime
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail

private theorem endpoint_positive {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q) : 1 ≤ N := by
  rcases hN with rfl | rfl
  · exact strictInteger_pos hq
  · exact (maximalInteger_spec hq).1

private theorem active_of_mem {N p : ℕ} (hN : 1 ≤ N)
    (hp : p ∈ N.primeFactors) : 1 ≤ N.factorization p := by
  exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
    (by omega) (Nat.dvd_of_mem_primeFactors hp)

private theorem largest_mem {N : ℕ} (hu : 2 ≤ largestPrime N) :
    largestPrime N ∈ N.primeFactors := by
  have hne : N.primeFactors.Nonempty := by
    by_contra h
    have hempty : N.primeFactors = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : largestPrime N = 0 := by simp [largestPrime, hempty]
    omega
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup N.primeFactors hne id
  have heq : largestPrime N = p := hmax
  exact heq.symm ▸ hp

private theorem endpoint_first_selected {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hp : p.Prime) (ha : 1 ≤ N.factorization p) :
    q ≤ goldenLayerMarginal p 1 := by
  rcases hN with rfl | rfl
  · exact ((strict_layer_iff hq hp (by omega : 1 ≤ (1 : ℕ))).mp ha).le
  · exact (weak_layer_iff hq hp (by omega : 1 ≤ (1 : ℕ))).mp ha

private theorem endpoint_prime_mem_of_le {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 2 ≤ largestPrime N) (hp : p.Prime) (hpu : p ≤ largestPrime N) :
    p ∈ N.primeFactors := by
  have hpositive := endpoint_positive hq hN
  have huMem := largest_mem hu
  by_cases heq : p = largestPrime N
  · simpa only [heq] using huMem
  have huPrime := Nat.prime_of_mem_primeFactors huMem
  have huPrice := endpoint_first_selected hq hN huPrime (active_of_mem hpositive huMem)
  have hgain : q < goldenLayerMarginal p 1 :=
    huPrice.trans_lt (golden_layer_marginal_one_strictAnti hp huPrime (by omega))
  have ha : 1 ≤ N.factorization p := by
    rcases hN with rfl | rfl
    · exact (strict_layer_iff hq hp (by omega : 1 ≤ (1 : ℕ))).mpr hgain
    · exact (weak_layer_iff hq hp (by omega : 1 ≤ (1 : ℕ))).mpr hgain.le
  exact hp.mem_primeFactors (Nat.dvd_of_factorization_pos (by omega)) (by omega)

private theorem endpoint_missing_first {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hp : p.Prime) (hnot : p ∉ N.primeFactors) :
    goldenLayerMarginal p 1 ≤ q := by
  have hpositive := endpoint_positive hq hN
  have hopt : IsGoldenResourceOptimal q N := by
    rcases hN with rfl | rfl
    · exact strict_is_optimal hq
    · exact (maximalInteger_spec hq).2.2.1
  have hnotdvd : ¬ p ∣ N := by
    intro hdvd
    exact hnot (hp.mem_primeFactors hdvd (by omega))
  have hnext := ((golden_resource_optimal_iff_layer_thresholds hq hpositive).mp hopt).1 p hp
  simpa only [Nat.factorization_eq_zero_of_not_dvd hnotdvd, Nat.zero_add] using hnext

private theorem first_marginal_lower {p : ℕ} (hp : p.Prime) :
    1 / (((p : ℝ) + 1) * Real.log p) ≤ goldenLayerMarginal p 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < 1 + 1 / (p : ℝ) by positivity)
  have hidentity : 1 - (1 + 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) + 1) := by
    field_simp
    ring
  rw [hidentity] at hlog
  rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
  calc
    1 / (((p : ℝ) + 1) * Real.log p) =
        (1 / ((p : ℝ) + 1)) / Real.log p := by rw [div_div]
    _ ≤ Real.log (1 + 1 / (p : ℝ)) / Real.log p :=
      (div_le_div_iff_of_pos_right hp.log_pos).mpr hlog

/-- The same endpoint's omitted Bertrand prime forces this lower price.
No cutoff-price hypothesis is supplied by the caller. -/
theorem endpoint_price_lower_of_largest {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 2 ≤ largestPrime N) :
    1 / ((2 * (largestPrime N : ℝ) + 1) * Real.log (2 * (largestPrime N : ℝ))) ≤ q := by
  obtain ⟨v, hv, huv, hv2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (largestPrime N) (by omega)
  have hvNot : v ∉ N.primeFactors := by
    intro hmem
    have hle : v ≤ largestPrime N := Finset.le_sup (f := id) hmem
    omega
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv.pos
  have hv2R : (v : ℝ) ≤ 2 * (largestPrime N : ℝ) := by exact_mod_cast hv2
  have hdenPos : 0 < ((v : ℝ) + 1) * Real.log v := mul_pos (by positivity) hv.log_pos
  have hdenLe : ((v : ℝ) + 1) * Real.log v ≤
      (2 * (largestPrime N : ℝ) + 1) * Real.log (2 * (largestPrime N : ℝ)) := by
    apply mul_le_mul (by linarith : (v : ℝ) + 1 ≤ 2 * (largestPrime N : ℝ) + 1)
      (Real.log_le_log hv0 hv2R) hv.log_pos.le
    positivity
  exact (one_div_le_one_div_of_le hdenPos hdenLe).trans
    ((first_marginal_lower hv).trans (endpoint_missing_first hq hN hv hvNot))

private theorem denominator_strict_gap {u : ℝ} (hu : 2 ≤ u) {p : ℕ}
    (hp : p.Prime) (hpu : 2 * Real.sqrt u ≤ (p : ℝ)) :
    (2 * u + 1) * Real.log (2 * u) < (p : ℝ) ^ 2 * Real.log p := by
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hs2 := Real.sq_sqrt hu0.le
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlogU := Real.log_le_sub_one_of_pos hu0
  have hgap : 0 < (2 * u - 1) * Real.log 2 - Real.log u := by
    have hmul := mul_nonneg (by linarith : 0 ≤ 2 * u - 1) (sub_nonneg.mpr hlogTwo)
    nlinarith
  have hpSq : 4 * u ≤ (p : ℝ) ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ 2 * Real.sqrt u) hpu
    nlinarith
  have hpLog : Real.log 2 + Real.log u / 2 ≤ Real.log p := by
    have h := Real.log_le_log (by positivity : 0 < 2 * Real.sqrt u) hpu
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs0.ne', Real.log_sqrt hu0.le] at h
    exact h
  calc
    (2 * u + 1) * Real.log (2 * u) < 4 * u * (Real.log 2 + Real.log u / 2) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hu0.ne']
      nlinarith
    _ ≤ 4 * u * Real.log p := mul_le_mul_of_nonneg_left hpLog (by positivity)
    _ ≤ (p : ℝ) ^ 2 * Real.log p := mul_le_mul_of_nonneg_right hpSq hp.log_pos.le

private theorem endpoint_second_layer_lt {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 2 ≤ largestPrime N) (hp : p.Prime)
    (hpu : 2 * Real.sqrt (largestPrime N : ℝ) ≤ (p : ℝ)) :
    goldenLayerMarginal p 2 < q := by
  have huR : (2 : ℝ) ≤ (largestPrime N : ℝ) := by exact_mod_cast hu
  have hdenPos : 0 < (2 * (largestPrime N : ℝ) + 1) *
      Real.log (2 * (largestPrime N : ℝ)) := by
    apply mul_pos (by positivity)
    apply Real.log_pos
    linarith
  calc
    goldenLayerMarginal p 2 ≤ (p : ℝ)⁻¹ ^ 2 / Real.log p :=
      golden_layer_marginal_le_inv_pow hp (by omega)
    _ = 1 / ((p : ℝ) ^ 2 * Real.log p) := by
      rw [inv_pow, ← one_div, div_div]
    _ < 1 / ((2 * (largestPrime N : ℝ) + 1) * Real.log (2 * (largestPrime N : ℝ))) :=
      one_div_lt_one_div_of_lt hdenPos (denominator_strict_gap huR hp hpu)
    _ ≤ q := endpoint_price_lower_of_largest hq hN hu

/-- Every actual support prime in this band has exactly its first layer.
The strict second-layer separation handles both endpoint tie conventions. -/
theorem endpoint_first_layer_band {q : ℝ} (hq : 0 < q) {N p : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 2 ≤ largestPrime N) (hp : p.Prime)
    (hlo : 2 * Real.sqrt (largestPrime N : ℝ) ≤ (p : ℝ))
    (hhi : p ≤ largestPrime N) :
    p ∈ N.primeFactors ∧ N.factorization p = 1 := by
  have hmem := endpoint_prime_mem_of_le hq hN hu hp hhi
  have ha := active_of_mem (endpoint_positive hq hN) hmem
  have hsecond := endpoint_second_layer_lt hq hN hu hp hlo
  have hnot : ¬ 2 ≤ N.factorization p := by
    intro htwo
    rcases hN with rfl | rfl
    · have h := (strict_layer_iff hq hp (by omega : 1 ≤ (2 : ℕ))).mp htwo
      linarith
    · have h := (weak_layer_iff hq hp (by omega : 1 ≤ (2 : ℕ))).mp htwo
      linarith
  exact ⟨hmem, by omega⟩

private theorem layer_nonneg {N p : ℕ} (hp : p ∈ N.primeFactors) :
    0 ≤ layerTail N p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hi1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hp0).mpr (by exact_mod_cast hprime.one_lt)
  have hx0 : 0 ≤ (p : ℝ)⁻¹ ^ (N.factorization p + 1) := pow_nonneg hi0.le _
  have hx1 : (p : ℝ)⁻¹ ^ (N.factorization p + 1) < 1 :=
    pow_lt_one₀ hi0.le hi1 (by omega)
  have h := Real.log_nonpos (by linarith : 0 ≤ 1 - (p : ℝ)⁻¹ ^ (N.factorization p + 1))
    (by linarith : 1 - (p : ℝ)⁻¹ ^ (N.factorization p + 1) ≤ 1)
  simpa only [layerTail, neg_nonneg] using h

private theorem first_layer_gt_inv_sq {N p : ℕ} (hp : p.Prime)
    (ha : N.factorization p = 1) :
    1 / (p : ℝ) ^ 2 < layerTail N p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hi1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hp0).mpr (by exact_mod_cast hp.one_lt)
  have hx0 : 0 < (p : ℝ)⁻¹ ^ 2 := pow_pos hi0 _
  have hx1 : (p : ℝ)⁻¹ ^ 2 < 1 := pow_lt_one₀ hi0.le hi1 (by norm_num)
  have hlog := Real.log_lt_sub_one_of_pos
    (by linarith : 0 < 1 - (p : ℝ)⁻¹ ^ 2)
    (by linarith : 1 - (p : ℝ)⁻¹ ^ 2 ≠ 1)
  have hinv : (p : ℝ)⁻¹ ^ 2 = 1 / (p : ℝ) ^ 2 := by rw [inv_pow, one_div]
  simp only [layerTail, ha, Nat.reduceAdd]
  rw [← hinv]
  linarith

/-- A complete Euler-tail lower bound for the same original endpoint.
Bertrand is applied at floor(2 sqrt u); every remaining prime and layer
stays in the actual tail, with its nonnegative contribution. -/
theorem endpoint_tail_gt_inv_sixteen_mul_largest {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 16 ≤ largestPrime N) :
    1 / (16 * (largestPrime N : ℝ)) < tail N := by
  classical
  let u : ℝ := largestPrime N
  let s : ℝ := Real.sqrt u
  let n : ℕ := ⌊2 * s⌋₊
  have huR : (16 : ℝ) ≤ u := by
    change (16 : ℝ) ≤ (largestPrime N : ℝ)
    exact_mod_cast hu
  have hu0 : 0 < u := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg u
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hs4 : (4 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact huR
  have hn1 : 1 ≤ n := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ 2 * s)).mpr
    norm_num
    linarith
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hpLo : 2 * s < (p : ℝ) := Nat.lt_of_floor_lt hnp
  have hfloor : (n : ℝ) ≤ 2 * s := Nat.floor_le (by positivity : 0 ≤ 2 * s)
  have hpHi : (p : ℝ) ≤ 4 * s := by
    have hpnR : (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpn
    linarith
  have hfour : 4 * s ≤ u := by
    have hmul := mul_nonneg hs0 (sub_nonneg.mpr hs4)
    nlinarith only [hmul, hs2]
  have hpuR : (p : ℝ) ≤ u := hpHi.trans hfour
  have hpu : p ≤ largestPrime N := by
    change (p : ℝ) ≤ (largestPrime N : ℝ) at hpuR
    exact_mod_cast hpuR
  have hband := endpoint_first_layer_band hq hN (by omega : 2 ≤ largestPrime N)
    hp (show 2 * Real.sqrt (largestPrime N : ℝ) ≤ (p : ℝ) from hpLo.le) hpu
  have hpSq : (p : ℝ) ^ 2 ≤ 16 * u := by
    have h := mul_self_le_mul_self (by exact_mod_cast hp.pos.le : (0 : ℝ) ≤ p) hpHi
    nlinarith
  have hpSq0 : 0 < (p : ℝ) ^ 2 := pow_pos (by exact_mod_cast hp.pos) _
  have hsingle : layerTail N p ≤ tail N := by
    exact Finset.single_le_sum (fun r hr => layer_nonneg hr) hband.1
  calc
    1 / (16 * (largestPrime N : ℝ)) ≤ 1 / (p : ℝ) ^ 2 :=
      one_div_le_one_div_of_le hpSq0 hpSq
    _ < layerTail N p := first_layer_gt_inv_sq hp hband.2
    _ ≤ tail N := hsingle

private theorem theta_sub_eq_prime_band_sum {A B : ℝ} (hAB : A ≤ B) :
    Chebyshev.theta B - Chebyshev.theta A =
      ∑ p ∈ Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊, Real.log (p : ℝ) := by
  classical
  have hsub : Nat.primesLE ⌊A⌋₊ ⊆ Nat.primesLE ⌊B⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono hAB)
  have hpartition := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  linarith only [hpartition]

/-- The complete tail controls the actual theta mass in any first-layer
band. The original integer and all nonnegative complementary layers stay
inside `tail N`; no prime-density or endpoint-sign premise is supplied. -/
theorem endpoint_tail_ge_theta_band {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 2 ≤ largestPrime N) {A B : ℝ}
    (hA : 2 * Real.sqrt (largestPrime N : ℝ) ≤ A)
    (hAB : A ≤ B) (hB : B ≤ (largestPrime N : ℝ)) :
    (Chebyshev.theta B - Chebyshev.theta A) / (B ^ 2 * Real.log B) ≤ tail N := by
  classical
  have huR : (2 : ℝ) ≤ (largestPrime N : ℝ) := by exact_mod_cast hu
  have hs1 : (1 : ℝ) ≤ Real.sqrt (largestPrime N : ℝ) :=
    Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hA1 : 1 < A := by linarith
  have hB1 : 1 < B := hA1.trans_le hAB
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos hB1
  have hden : 0 < B ^ 2 * Real.log B := mul_pos (pow_pos hB0 _) hlogB
  let S : Finset ℕ := Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊
  have hbandFacts (p : ℕ) (hp : p ∈ S) :
      p.Prime ∧ A < (p : ℝ) ∧ (p : ℝ) ≤ B := by
    obtain ⟨hpB, hpA⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpFloor, hprime⟩ := Nat.mem_primesLE.mp hpB
    have hpBR : (p : ℝ) ≤ B := (Nat.le_floor_iff hB0.le).mp hpFloor
    have hpAR : A < (p : ℝ) := by
      by_contra h
      exact hpA (Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff hA0).mpr (le_of_not_gt h), hprime⟩)
    exact ⟨hprime, hpAR, hpBR⟩
  have hselected (p : ℕ) (hp : p ∈ S) :
      p ∈ N.primeFactors ∧ N.factorization p = 1 := by
    have hf := hbandFacts p hp
    have hpU : p ≤ largestPrime N := by exact_mod_cast hf.2.2.trans hB
    exact endpoint_first_layer_band hq hN hu hf.1 (hA.trans hf.2.1.le) hpU
  have hweight (p : ℕ) (hp : p ∈ S) :
      Real.log (p : ℝ) / (B ^ 2 * Real.log B) ≤ layerTail N p := by
    have hf := hbandFacts p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hf.1.pos
    have hpSq0 : 0 < (p : ℝ) ^ 2 := pow_pos hp0 _
    have hpSq : (p : ℝ) ^ 2 ≤ B ^ 2 := by
      have h := mul_self_le_mul_self hp0.le hf.2.2
      nlinarith only [h]
    have hratio : (1 : ℝ) ≤ B ^ 2 / (p : ℝ) ^ 2 :=
      (le_div_iff₀ hpSq0).mpr (by simpa using hpSq)
    have hlogP : Real.log (p : ℝ) ≤ Real.log B := Real.log_le_log hp0 hf.2.2
    have hscaled := mul_le_mul_of_nonneg_right hratio hlogB.le
    have hlower : Real.log (p : ℝ) / (B ^ 2 * Real.log B) ≤ 1 / (p : ℝ) ^ 2 := by
      apply (div_le_iff₀ hden).mpr
      calc
        Real.log (p : ℝ) ≤ Real.log B := hlogP
        _ ≤ (B ^ 2 / (p : ℝ) ^ 2) * Real.log B := by simpa using hscaled
        _ = (1 / (p : ℝ) ^ 2) * (B ^ 2 * Real.log B) := by ring
    exact hlower.trans (first_layer_gt_inv_sq hf.1 (hselected p hp).2).le
  have hsub : S ⊆ N.primeFactors := fun p hp => (hselected p hp).1
  rw [theta_sub_eq_prime_band_sum hAB]
  change (∑ p ∈ S, Real.log (p : ℝ)) / (B ^ 2 * Real.log B) ≤ tail N
  calc
    (∑ p ∈ S, Real.log (p : ℝ)) / (B ^ 2 * Real.log B) =
        ∑ p ∈ S, Real.log (p : ℝ) / (B ^ 2 * Real.log B) := by rw [Finset.sum_div]
    _ ≤ ∑ p ∈ S, layerTail N p := Finset.sum_le_sum hweight
    _ ≤ tail N := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => layer_nonneg hp)

/-- Explicit Chebyshev mass available in the same endpoint's
`(2 sqrt u, 8 sqrt u]` first-layer band. It may be negative at small u. -/
def chebyshevBandLower (u : ℝ) : ℝ :=
  (4 * Real.sqrt u - 1) * Real.log 2 - Real.log (8 * Real.sqrt u + 2) -
    2 * Real.sqrt (8 * Real.sqrt u) * Real.log (8 * Real.sqrt u)

/-- An explicit all-price lower bound using only the existing Chebyshev
theorems. `max 0` handles small bands without assuming they contain primes. -/
theorem endpoint_tail_ge_chebyshev {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 64 ≤ largestPrime N) :
    max 0 (chebyshevBandLower (largestPrime N : ℝ)) /
      (64 * (largestPrime N : ℝ) * Real.log (8 * Real.sqrt (largestPrime N : ℝ))) ≤
        tail N := by
  let u : ℝ := largestPrime N
  let s : ℝ := Real.sqrt u
  have huR : (64 : ℝ) ≤ u := by
    change (64 : ℝ) ≤ (largestPrime N : ℝ)
    exact_mod_cast hu
  have hu0 : 0 < u := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg u
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hs8 : (8 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact huR
  have hAB : 2 * s ≤ 8 * s := by linarith
  have hB : 8 * s ≤ u := by
    have hmul := mul_nonneg hs0 (sub_nonneg.mpr hs8)
    nlinarith only [hmul, hs2]
  have hband := endpoint_tail_ge_theta_band hq hN (by omega : 2 ≤ largestPrime N)
    (A := 2 * s) (B := 8 * s) le_rfl hAB hB
  have hthetaLower := Chebyshev.theta_ge' (x := 8 * s) (by linarith : 1 ≤ 8 * s)
  have hthetaUpper := Chebyshev.theta_le_log4_mul_x (x := 2 * s) (by positivity)
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    <;> norm_num
  rw [hlogFour] at hthetaUpper
  have hE : chebyshevBandLower u ≤ Chebyshev.theta (8 * s) - Chebyshev.theta (2 * s) := by
    dsimp only [chebyshevBandLower]
    change (4 * s - 1) * Real.log 2 - Real.log (8 * s + 2) -
      2 * Real.sqrt (8 * s) * Real.log (8 * s) ≤ _
    nlinarith only [hthetaLower, hthetaUpper]
  have hthetaNonneg : 0 ≤ Chebyshev.theta (8 * s) - Chebyshev.theta (2 * s) :=
    sub_nonneg.mpr (Chebyshev.theta_mono hAB)
  have hmax := max_le hthetaNonneg hE
  have hdenPos : 0 < 64 * u * Real.log (8 * s) := by
    apply mul_pos (by positivity)
    apply Real.log_pos
    linarith
  have hdenEq : (8 * s) ^ 2 * Real.log (8 * s) = 64 * u * Real.log (8 * s) := by
    calc
      (8 * s) ^ 2 * Real.log (8 * s) = 64 * s ^ 2 * Real.log (8 * s) := by ring
      _ = 64 * u * Real.log (8 * s) := by rw [hs2]
  change max 0 (chebyshevBandLower u) / (64 * u * Real.log (8 * s)) ≤ tail N
  apply le_trans (div_le_div_of_nonneg_right hmax hdenPos.le)
  simpa only [hdenEq] using hband

private theorem chebyshevBandLower_ge_sqrt_log_two {u : ℝ} (hu : (2 : ℝ) ^ 22 ≤ u) :
    2 * Real.sqrt u * Real.log 2 ≤ chebyshevBandLower u := by
  let s : ℝ := Real.sqrt u
  let t : ℝ := 8 * s
  let r : ℝ := Real.sqrt t
  let z : ℝ := r / 128
  have huBig : (4194304 : ℝ) ≤ u := by norm_num at hu ⊢; exact hu
  have hs2048 : (2048 : ℝ) ≤ s := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact huBig
  have htBig : (16384 : ℝ) ≤ t := by dsimp only [t]; linarith
  have ht0 : 0 < t := by linarith
  have hr128 : (128 : ℝ) ≤ r := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact htBig
  have hr0 : 0 ≤ r := Real.sqrt_nonneg t
  have hr2 : r ^ 2 = t := Real.sq_sqrt ht0.le
  have hz1 : (1 : ℝ) ≤ z := by dsimp only [z]; linarith
  have hz0 : 0 < z := by linarith
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htForm : t = (2 : ℝ) ^ 14 * z ^ 2 := by
    calc
      t = r ^ 2 := hr2.symm
      _ = (2 : ℝ) ^ 14 * z ^ 2 := by dsimp only [z]; ring
  have hlogT : Real.log t = 14 * Real.log 2 + 2 * Real.log z := by
    rw [htForm, Real.log_mul (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
      (pow_ne_zero _ hz0.ne'), Real.log_pow, Real.log_pow]
    <;> norm_num
  have hlogZ := Real.log_le_sub_one_of_pos hz0
  have hconst : 2 ≤ 14 * Real.log (2 : ℝ) := by linarith only [hlogTwo]
  have hscaled := mul_nonneg (sub_nonneg.mpr hconst) (sub_nonneg.mpr hz1)
  have hlogTupper : Real.log t ≤ (7 * Real.log 2 / 64) * r := by
    calc
      Real.log t ≤ 14 * Real.log 2 * z := by
        nlinarith only [hlogT, hlogZ, hscaled]
      _ = (7 * Real.log 2 / 64) * r := by dsimp only [z]; ring
  have hlarge : 2 * r * Real.log t ≤ (7 / 32 : ℝ) * t * Real.log 2 := by
    calc
      2 * r * Real.log t ≤ 2 * r * ((7 * Real.log 2 / 64) * r) :=
        mul_le_mul_of_nonneg_left hlogTupper (by positivity)
      _ = (7 / 32 : ℝ) * r ^ 2 * Real.log 2 := by ring
      _ = (7 / 32 : ℝ) * t * Real.log 2 := by rw [hr2]
  have hlogTplus : Real.log (t + 2) ≤ Real.log 2 + Real.log t := by
    have h := Real.log_le_log (by linarith : 0 < t + 2)
      (by linarith : t + 2 ≤ 2 * t)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne'] at h
  have hpoly : 2 + 7 * r / 64 ≤ t / 32 := by
    have hmul := mul_nonneg hr0 (sub_nonneg.mpr hr128)
    nlinarith only [hmul, hr2, hr128]
  have hsmall : Real.log 2 + Real.log (t + 2) ≤ (1 / 32 : ℝ) * t * Real.log 2 := by
    calc
      Real.log 2 + Real.log (t + 2) ≤ 2 * Real.log 2 + Real.log t := by
        linarith only [hlogTplus]
      _ ≤ Real.log 2 * (2 + 7 * r / 64) := by nlinarith only [hlogTupper]
      _ ≤ (1 / 32 : ℝ) * t * Real.log 2 := by
        have h := mul_le_mul_of_nonneg_left hpoly hlogTwoPos.le
        nlinarith only [h]
  have hEexpression : chebyshevBandLower u =
      (t / 2) * Real.log 2 - (Real.log 2 + Real.log (t + 2) + 2 * r * Real.log t) := by
    dsimp only [chebyshevBandLower, r, t, s]
    ring
  calc
    2 * Real.sqrt u * Real.log 2 = (t / 4) * Real.log 2 := by dsimp only [t, s]; ring
    _ ≤ chebyshevBandLower u := by
      rw [hEexpression]
      nlinarith only [hsmall, hlarge]

/-- A positive lower bound on the correct square-root/logarithmic scale,
for the same original endpoint at every positive price. The numerical
threshold is proved using elementary logarithm bounds, not a supplied
prime-density or final Robin-sign certificate. -/
theorem endpoint_tail_ge_sqrt_log {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 2 ^ 22 ≤ largestPrime N) :
    Real.log 2 / (32 * Real.sqrt (largestPrime N : ℝ) *
      Real.log (8 * Real.sqrt (largestPrime N : ℝ))) ≤ tail N := by
  let u : ℝ := largestPrime N
  let s : ℝ := Real.sqrt u
  have huNat : 4194304 ≤ largestPrime N := by norm_num at hu ⊢; exact hu
  have huR : (2 : ℝ) ^ 22 ≤ u := by
    change (2 : ℝ) ^ 22 ≤ (largestPrime N : ℝ)
    norm_num
    exact_mod_cast huNat
  have hu0 : 0 < u := by
    have h : (4194304 : ℝ) ≤ u := by
      change (4194304 : ℝ) ≤ (largestPrime N : ℝ)
      exact_mod_cast huNat
    linarith
  have hsPos : 0 < s := Real.sqrt_pos.mpr hu0
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hs1 : (1 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by
    norm_num
    have h : (4194304 : ℝ) ≤ u := by
      change (4194304 : ℝ) ≤ (largestPrime N : ℝ)
      exact_mod_cast huNat
    linarith)
  have hlogPos : 0 < Real.log (8 * s) := Real.log_pos (by linarith)
  have hdenPos : 0 < 64 * u * Real.log (8 * s) := mul_pos (by positivity) hlogPos
  have hE : 2 * s * Real.log 2 ≤ chebyshevBandLower u :=
    chebyshevBandLower_ge_sqrt_log_two huR
  have hnum : 2 * s * Real.log 2 ≤ max 0 (chebyshevBandLower u) :=
    hE.trans (le_max_right _ _)
  have hbase := endpoint_tail_ge_chebyshev hq hN (by omega : 64 ≤ largestPrime N)
  change Real.log 2 / (32 * s * Real.log (8 * s)) ≤ tail N
  calc
    Real.log 2 / (32 * s * Real.log (8 * s)) =
        (2 * s * Real.log 2) / (64 * u * Real.log (8 * s)) := by
      rw [← hs2]
      field_simp [hsPos.ne', hlogPos.ne']
      <;> ring
    _ ≤ max 0 (chebyshevBandLower u) / (64 * u * Real.log (8 * s)) :=
      div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ tail N := hbase

end D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
