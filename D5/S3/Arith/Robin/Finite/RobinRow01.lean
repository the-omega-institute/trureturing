/- GID: D5/S3/Arith/Robin/Finite/RobinRow01
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Finite/RobinRow01
   mirror-E: none(waiver:exact-rational-certificates-verified-in-Lean)
   anchors: []
   utility: none
   digest: Unique optimizer at the original Robin1984 Row 01 price, a strict log margin reserve on log-height [22,36], and the finite Robin inequality through 321253732800. -/

import D5.S3.Arith.GoldenResource.RobinRationalBasis
import D5.S3.Arith.Robin.ActualRobinInterval

/-!
# Robin1984 Row 01 at its original resource price

The price and six cutoffs come from Jonas Whidden's Robin1984 formalization,
`Robin1984.Finite.Certificates.Row01`, pinned at
https://github.com/kimihiro64/Robin1984/blob/5ce18bf3487c68d9353276ef5811057f60d17808/Robin1984/Finite/Certificates/Row01.lean.
The strict signs and the wider interval use the native rational logarithm bounds.
The integer consequence uses the native original-price bracketing theorem.
-/

namespace D5.S3.Arith.Robin.Finite.RobinRow01

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Weil.GronwallLowerEnvelope

noncomputable section

def row01Price : ℝ := 2565510579241 / 250000000000000

def row01Integer : ℕ := 321253732800

private theorem row01_price_pos : 0 < row01Price := by norm_num [row01Price]

private theorem row01_integer_pos : 1 ≤ row01Integer := by norm_num [row01Integer]

private def layerRatio (p k : ℕ) : ℝ :=
  (1 - (p : ℝ)⁻¹ ^ (k + 1)) / (1 - (p : ℝ)⁻¹ ^ k)

private theorem layer_ratio_eq_geometric {p k : ℕ} (hp : 1 < p) (hk : 1 ≤ k) :
    layerRatio p k = 1 + 1 / ((p : ℝ) * ∑ i ∈ range k, (p : ℝ) ^ i) := by
  let x : ℝ := p
  have hx : 1 < x := by
    change (1 : ℝ) < (p : ℝ)
    exact_mod_cast hp
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hpow : 1 < x ^ k := one_lt_pow₀ hx (by omega)
  have hpow0 : x ^ k ≠ 0 := (zero_lt_one.trans hpow).ne'
  let s := ∑ i ∈ range k, x ^ i
  have hs : 0 < s := by
    dsimp only [s]
    exact sum_pos (fun i _ => pow_pos (zero_lt_one.trans hx) i)
      ⟨0, mem_range.mpr (by omega)⟩
  have hgeom : s * (x - 1) = x ^ k - 1 := geom_sum_mul x k
  have hsub (y : ℝ) (hy : y ≠ 0) : 1 - y⁻¹ = (y - 1) / y := by
    field_simp [hy]
  change (1 - x⁻¹ ^ (k + 1)) / (1 - x⁻¹ ^ k) = 1 + 1 / (x * s)
  calc
    _ = 1 + (x - 1) / (x * (x ^ k - 1)) := by
      rw [inv_pow x (k + 1), inv_pow x k, pow_succ' x k,
        hsub _ (mul_ne_zero hx0 hpow0), hsub _ hpow0]
      have hsub0 : x ^ k - 1 ≠ 0 := (sub_pos.mpr hpow).ne'
      field_simp [hx0, hpow0, hsub0, div_ne_zero hsub0 hpow0]
      ring
    _ = _ := by
      rw [← hgeom]
      field_simp [hx0, hs.ne', (sub_pos.mpr hx).ne']

/-- At a fixed positive layer the marginal decreases with the base, including
the composite cutoff bases in the rational row. -/
private theorem golden_layer_marginal_antitone_base {p q k : ℕ}
    (hp : 1 < p) (hpq : p ≤ q) (hk : 1 ≤ k) :
    goldenLayerMarginal q k ≤ goldenLayerMarginal p k := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hqR : (1 : ℝ) < q := hpR.trans_le hpqR
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hqR
  let S (x : ℝ) := ∑ i ∈ range k, x ^ i
  have hS (x : ℝ) (hx : 0 < x) : 0 < S x :=
    sum_pos (fun i _ => pow_pos hx i) ⟨0, mem_range.mpr (by omega)⟩
  have hSle : S p ≤ S q :=
    sum_le_sum (fun i _ => pow_le_pow_left₀ hp0.le hpqR i)
  have hden : (p : ℝ) * S p ≤ (q : ℝ) * S q :=
    mul_le_mul hpqR hSle (hS _ hp0).le hq0.le
  have hr : 1 + 1 / ((q : ℝ) * S q) ≤ 1 + 1 / ((p : ℝ) * S p) :=
    add_le_add le_rfl (one_div_le_one_div_of_le (mul_pos hp0 (hS _ hp0)) hden)
  have hrq : 1 < 1 + 1 / ((q : ℝ) * S q) :=
    lt_add_of_pos_right _ (one_div_pos.mpr (mul_pos hq0 (hS _ hq0)))
  have hrp : 1 < 1 + 1 / ((p : ℝ) * S p) := hrq.trans_le hr
  change Real.log (layerRatio q k) / Real.log q ≤ Real.log (layerRatio p k) / Real.log p
  rw [layer_ratio_eq_geometric (hp.trans_le hpq) hk, layer_ratio_eq_geometric hp hk]
  calc
    _ ≤ Real.log (1 + 1 / ((p : ℝ) * S p)) / Real.log q :=
      div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans hrq) hr)
        (Real.log_pos hqR).le
    _ ≤ _ := div_le_div_of_nonneg_left (Real.log_pos hrp).le (Real.log_pos hpR)
      (Real.log_le_log hp0 hpqR)

private theorem log_near_one_bounds (x lo hi : ℝ) (hx1 : 1 ≤ x) (hx2 : x < 2)
    (hcalc : lo < atanhPartial (atanhParameter x) 3 ∧
      atanhPartial (atanhParameter x) 3 +
        2 * atanhParameter x ^ 7 / (7 * (1 - atanhParameter x ^ 2)) < hi) :
    lo < Real.log x ∧ Real.log x < hi := by
  have hs := log_expansion_remainder_bound hx1 hx2 3
  norm_num [logRemainder] at hs
  constructor
  · linarith only [hcalc.1, hs.1]
  · linarith only [hcalc.2, hs.2]

private theorem layer_above_of_bounds {p k : ℕ} {r lo hi : ℝ} (hp : 1 < p)
    (hr : layerRatio p k = r) (hpLog : Real.log (p : ℝ) < hi)
    (hrLog : lo < Real.log r) (hcalc : row01Price * hi ≤ lo) :
    row01Price < goldenLayerMarginal p k := by
  change row01Price < Real.log (layerRatio p k) / Real.log p
  rw [hr, lt_div_iff₀ (Real.log_pos (by exact_mod_cast hp))]
  exact ((mul_le_mul_of_nonneg_left hpLog.le row01_price_pos.le).trans hcalc).trans_lt hrLog

private theorem layer_below_of_bounds {p k : ℕ} {r lo hi : ℝ} (hp : 1 < p)
    (hr : layerRatio p k = r) (hpLog : lo < Real.log (p : ℝ))
    (hrLog : Real.log r < hi) (hcalc : hi ≤ row01Price * lo) :
    goldenLayerMarginal p k < row01Price := by
  change Real.log (layerRatio p k) / Real.log p < row01Price
  rw [hr, div_lt_iff₀ (Real.log_pos (by exact_mod_cast hp))]
  exact hrLog.trans_le (hcalc.trans (mul_le_mul_of_nonneg_left hpLog.le row01_price_pos.le))

private theorem row01_cut_signs :
    (row01Price < goldenLayerMarginal 28 1 ∧
      row01Price < goldenLayerMarginal 6 2 ∧
      row01Price < goldenLayerMarginal 3 3 ∧
      row01Price < goldenLayerMarginal 2 4 ∧
      row01Price < goldenLayerMarginal 2 5 ∧
      row01Price < goldenLayerMarginal 2 6) ∧
    (goldenLayerMarginal 29 1 < row01Price ∧
      goldenLayerMarginal 7 2 < row01Price ∧
      goldenLayerMarginal 4 3 < row01Price ∧
      goldenLayerMarginal 3 4 < row01Price ∧
      goldenLayerMarginal 3 5 < row01Price ∧
      goldenLayerMarginal 3 6 < row01Price ∧
      goldenLayerMarginal 2 7 < row01Price) := by
  have hlog2 := log_two_decimal_bounds
  have hlog3 := rational_log_bounds 3 (3 / 2)
    (1098608512 / 1000000000) (1098612325 / 1000000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog4 := rational_log_bounds 4 (1)
    (1386294359 / 1000000000) (1386294363 / 1000000000) 2 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog6 := rational_log_bounds 6 (3 / 2)
    (1791755692 / 1000000000) (1791759506 / 1000000000) 2 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog7 := rational_log_bounds 7 (7 / 4)
    (1945876106 / 1000000000) (1945910752 / 1000000000) 2 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog28 := rational_log_bounds 28 (7 / 4)
    (3332170467 / 1000000000) (3332205114 / 1000000000) 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog29 := rational_log_bounds 29 (29 / 16)
    (3367244506 / 1000000000) (3367296858 / 1000000000) 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have hr := log_near_one_bounds (29 / 28) (35091318 / 1000000000)
      (35091321 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_above_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog28.2 hr.1
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (43 / 42) (23530496 / 1000000000)
      (23530499 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_above_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog6.2 hr.1
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (40 / 39) (25317806 / 1000000000)
      (25317809 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_above_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog3.2 hr.1
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (31 / 30) (32789821 / 1000000000)
      (32789824 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_above_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog2.2 hr.1
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (63 / 62) (16000340 / 1000000000)
      (16000343 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_above_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog2.2 hr.1
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (127 / 126) (7905178 / 1000000000)
      (7905181 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_above_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog2.2 hr.1
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (30 / 29) (33901550 / 1000000000)
      (33901553 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_below_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog29.1 hr.2
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (57 / 56) (17699576 / 1000000000)
      (17699579 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_below_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog7.1 hr.2
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (85 / 84) (11834456 / 1000000000)
      (11834459 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_below_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog4.1 hr.2
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (121 / 120) (8298801 / 1000000000)
      (8298804 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_below_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog3.1 hr.2
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (364 / 363) (2751032 / 1000000000)
      (2751035 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_below_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog3.1 hr.2
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (1093 / 1092) (915330 / 1000000000)
      (915333 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_below_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog3.1 hr.2
      (by norm_num [row01Price])
  · have hr := log_near_one_bounds (255 / 254) (3929277 / 1000000000)
      (3929280 / 1000000000) (by norm_num) (by norm_num)
      (by norm_num [atanhParameter, atanhPartial, Finset.sum_range_succ])
    exact layer_below_of_bounds (by norm_num)
      (by norm_num [layerRatio]) hlog2.1 hr.2
      (by norm_num [row01Price])

private def row01Cut (k : ℕ) : ℕ :=
  if k = 1 then 28 else if k = 2 then 6 else if k = 3 then 3 else 2

private def row01Exponent (p : ℕ) : ℕ :=
  if 2 = p then 6 else if 3 = p then 3 else if 5 = p then 2 else
  if 7 = p then 1 else if 11 = p then 1 else if 13 = p then 1 else
  if 17 = p then 1 else if 19 = p then 1 else if 23 = p then 1 else 0

private theorem row01_integer_product :
    row01Integer = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 1 * 11 ^ 1 * 13 ^ 1 * 17 ^ 1 * 19 ^ 1 * 23 ^ 1 := by
  norm_num [row01Integer]

private theorem row01_factorization (p : ℕ) :
    row01Integer.factorization p = row01Exponent p := by
  rw [row01_integer_product]
  rw [Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    (by norm_num : Nat.Prime 2).factorization_pow,
    (by norm_num : Nat.Prime 3).factorization_pow,
    (by norm_num : Nat.Prime 5).factorization_pow,
    (by norm_num : Nat.Prime 7).factorization_pow,
    (by norm_num : Nat.Prime 11).factorization_pow,
    (by norm_num : Nat.Prime 13).factorization_pow,
    (by norm_num : Nat.Prime 17).factorization_pow,
    (by norm_num : Nat.Prime 19).factorization_pow,
    (by norm_num : Nat.Prime 23).factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply, row01Exponent]
  split_ifs <;> omega

private theorem row01_cut_membership {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (h6 : k ≤ 6) :
    p ≤ row01Cut k ↔ k ≤ row01Exponent p := by
  by_cases h29 : 29 ≤ p
  · have hzero : row01Exponent p = 0 := by
      unfold row01Exponent
      split_ifs <;> omega
    have hcut : row01Cut k ≤ 28 := by
      unfold row01Cut
      split_ifs <;> decide
    rw [hzero]
    omega
  · have hp2 := hp.two_le
    have hp28 : p ≤ 28 := by omega
    interval_cases p <;> norm_num at hp <;>
      interval_cases k <;> norm_num [row01Cut, row01Exponent]

/-- The checked cuts classify every positive layer of every prime at the row price. -/
private theorem row01_layer_signs {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (k ≤ row01Integer.factorization p → row01Price < goldenLayerMarginal p k) ∧
    (row01Integer.factorization p < k → goldenLayerMarginal p k < row01Price) := by
  rcases row01_cut_signs with
    ⟨⟨ht1, ht2, ht3, ht4, ht5, ht6⟩, ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7⟩⟩
  rw [row01_factorization]
  by_cases h6 : k ≤ 6
  · have htop : row01Price < goldenLayerMarginal (row01Cut k) k := by
      interval_cases k <;> first | exact ht1 | exact ht2 | exact ht3 | exact ht4 | exact ht5 | exact ht6
    have hnext : goldenLayerMarginal (row01Cut k + 1) k < row01Price := by
      interval_cases k <;> first | exact hn1 | exact hn2 | exact hn3 | exact hn4 | exact hn5 | exact hn6
    have hcut2 : 1 < row01Cut k + 1 := by
      unfold row01Cut
      split_ifs <;> decide
    have hmem := row01_cut_membership hp hk h6
    constructor
    · intro h
      exact htop.trans_le (golden_layer_marginal_antitone_base hp.one_lt (hmem.mpr h) hk)
    · intro h
      have hle : row01Cut k + 1 ≤ p := by
        by_contra! hlt
        have := hmem.mp (show p ≤ row01Cut k by omega)
        omega
      exact (golden_layer_marginal_antitone_base hcut2 hle hk).trans_lt hnext
  · have hexp : row01Exponent p ≤ 6 := by
      unfold row01Exponent
      split_ifs <;> decide
    have hseven : goldenLayerMarginal p 7 < row01Price :=
      (golden_layer_marginal_antitone_base (by norm_num) hp.two_le (by norm_num)).trans_lt hn7
    constructor
    · intro h
      omega
    · intro _
      rcases eq_or_lt_of_le (show 7 ≤ k by omega) with heq | hlt
      · simpa only [← heq] using hseven
      · exact (golden_layer_strict_decrease hp (by norm_num) hlt).trans hseven

/-- The native objective is maximized by the exact row product at the original price. -/
private theorem row01_optimal : IsGoldenResourceOptimal row01Price row01Integer := by
  apply (golden_resource_optimal_iff_layer_thresholds row01_price_pos row01_integer_pos).mpr
  constructor
  · intro p hp
    exact ((row01_layer_signs hp (by omega)).2 (by omega)).le
  · intro p hp hdiv
    have hval := hp.factorization_pos_of_dvd (by norm_num [row01Integer]) hdiv
    exact ((row01_layer_signs hp hval).1 le_rfl).le

/-- The Row 01 product is the unique positive integer maximizing the original objective. -/
theorem row01_optimal_iff {m : ℕ} (hm : 1 ≤ m) :
    IsGoldenResourceOptimal row01Price m ↔ m = row01Integer := by
  constructor
  · intro hopt
    have ht := (golden_resource_optimal_iff_layer_thresholds row01_price_pos hm).mp hopt
    apply Nat.eq_of_factorization_eq (by omega) (by norm_num [row01Integer])
    intro p
    by_cases hp : p.Prime
    · apply le_antisymm
      · by_contra! hlt
        have hpos : 1 ≤ m.factorization p := by omega
        have hd := Nat.dvd_of_factorization_pos (by omega : m.factorization p ≠ 0)
        exact (not_lt_of_ge (ht.2 p hp hd)) ((row01_layer_signs hp hpos).2 hlt)
      · by_contra! hlt
        have hg := (row01_layer_signs (k := m.factorization p + 1) hp (by omega)).1 (by omega)
        exact (not_lt_of_ge (ht.1 p hp)) hg
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · rintro rfl
    exact row01_optimal

private theorem row01_maximal_integer : maximalInteger row01Price = row01Integer :=
  (row01_optimal_iff (maximalInteger_spec row01_price_pos).1).mp
    (maximalInteger_spec row01_price_pos).2.2.1

private theorem row01_sigma : ArithmeticFunction.sigma 1 row01Integer = 1828682956800 := by
  rw [row01_integer_product]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by decide),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
  norm_num [Finset.sum_range_succ]

private theorem row01_log_height :
    (26495497076 / 1000000000 : ℝ) < Real.log (row01Integer : ℝ) ∧
      Real.log (row01Integer : ℝ) < (26495497103 / 1000000000 : ℝ) := by
  refine rational_log_bounds _ (5019589575 / 4294967296) _ _ 38 3
    (by norm_num [row01Integer]) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem row01_objective_upper :
    goldenResourceObjective row01Price row01Integer <
      (1739120047 / 1000000000 : ℝ) - row01Price * (26495497076 / 1000000000) := by
  have hratio :
      (ArithmeticFunction.sigma 1 row01Integer : ℝ) / row01Integer = 6047232 / 1062347 := by
    rw [row01_sigma]
    norm_num [row01Integer]
  have hlog := rational_log_bounds (6047232 / 1062347) (1511808 / 1062347)
    (1739118585 / 1000000000) (1739120047 / 1000000000) 2 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hheight := mul_le_mul_of_nonneg_left row01_log_height.1.le row01_price_pos.le
  rw [golden_resource_sigma_identity _ row01_integer_pos, hratio]
  linarith only [hlog.2, hheight]

private def row01SupportGap (H : ℝ) : ℝ :=
  robinThreshold H - row01Price * H - goldenResourceObjective row01Price row01Integer

private theorem row01_endpoint_reserve {H lower : ℝ}
    (hloglog : lower < Real.log (Real.log H))
    (hcalc : (1 / 80 : ℝ) ≤
      5772155 / 10000000 + lower - row01Price * H -
        (1739120047 / 1000000000 - row01Price * (26495497076 / 1000000000))) :
    (1 / 80 : ℝ) < row01SupportGap H := by
  unfold row01SupportGap robinThreshold
  linarith only [eulerMascheroni_decimal_bounds.1, hloglog, hcalc, row01_objective_upper]

private theorem row01_endpoint_reserve_left : (1 / 80 : ℝ) < row01SupportGap 22 := by
  have h22 := rational_log_bounds 22 (11 / 8) (3091 / 1000) (3091042460 / 1000000000) 4 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog := rational_log_bounds (3091 / 1000) (3091 / 2000)
    (1128488511 / 1000000000) (1128494730 / 1000000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact row01_endpoint_reserve
    (hlog.1.trans (Real.log_lt_log (by norm_num) h22.1)) (by norm_num [row01Price])

private theorem row01_endpoint_reserve_right : (1 / 80 : ℝ) < row01SupportGap 36 := by
  have h36 := rational_log_bounds 36 (9 / 8) (3583 / 1000) (3583518941 / 1000000000) 5 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog := rational_log_bounds (3583 / 1000) (3583 / 2000)
    (1276155524 / 1000000000) (1276201302 / 1000000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact row01_endpoint_reserve
    (hlog.1.trans (Real.log_lt_log (by norm_num) h36.1)) (by norm_num [row01Price])

private theorem row01_interval_reserve {H : ℝ} (h22 : 22 ≤ H) (h36 : H ≤ 36) :
    (1 / 80 : ℝ) < row01SupportGap H := by
  let t : ℝ := (H - 22) / 14
  have ht0 : 0 ≤ t := by dsimp [t]; linarith only [h22]
  have ht1 : t ≤ 1 := by dsimp [t]; linarith only [h36]
  have hheight : (1 - t) * 22 + t * 36 = H := by dsimp [t]; ring
  have hconcave := threshold_strictConcaveOn.concaveOn.2
    (show (22 : ℝ) ∈ Set.Ioi (1 : ℝ) by norm_num)
    (show (36 : ℝ) ∈ Set.Ioi (1 : ℝ) by norm_num)
    (sub_nonneg.mpr ht1) ht0 (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul, hheight] at hconcave
  let c := min (row01SupportGap 22) (row01SupportGap 36)
  have hc : (1 / 80 : ℝ) < c :=
    lt_min row01_endpoint_reserve_left row01_endpoint_reserve_right
  have hleft : (1 - t) * c ≤ (1 - t) * row01SupportGap 22 :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr ht1)
  have hright : t * c ≤ t * row01SupportGap 36 :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) ht0
  have hlinear : row01Price * ((1 - t) * 22 + t * 36) = row01Price * H :=
    congrArg (fun x : ℝ => row01Price * x) hheight
  have hchord :
      (1 - t) * row01SupportGap 22 + t * row01SupportGap 36 ≤ row01SupportGap H := by
    unfold row01SupportGap
    nlinarith only [hconcave, hlinear]
  exact hc.trans_le (calc
    c = (1 - t) * c + t * c := by ring
    _ ≤ _ := add_le_add hleft hright
    _ ≤ _ := hchord)

/-- The strict reserve plus the exact objective deficit at the original Row 01 price. -/
theorem robin_log_margin_fixed_price_row01 {n : ℕ}
    (h22 : 22 ≤ Real.log (n : ℝ)) (h36 : Real.log (n : ℝ) ≤ 36) :
    (1 / 80 : ℝ) + goldenResourceObjective row01Price row01Integer -
      goldenResourceObjective row01Price n < robinLogMargin n := by
  have hn : 1 ≤ n := by
    by_contra! h
    have hz : n = 0 := by omega
    subst n
    norm_num at h22
  have hgap := row01_interval_reserve h22 h36
  rw [golden_resource_sigma_identity row01Price hn, margin_eq_threshold_sub_W]
  unfold row01SupportGap at hgap
  unfold W
  linarith only [hgap]

private def row01Primes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23}

private theorem row01_primeFactors : row01Integer.primeFactors = row01Primes := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, row01_factorization]
  simp only [row01Primes, Finset.mem_insert, Finset.mem_singleton, row01Exponent]
  split_ifs <;> simp_all [eq_comm]

private theorem row01_prime_count : row01Primes.card = 9 := by decide

private theorem row01_prime_product : (∏ p ∈ row01Primes, p) = 223092870 := by decide

private theorem endpoint_mem_divisibility_interval {q : ℝ} (hq : 0 < q)
    {N : ℕ} (hN : N = strictInteger q ∨ N = maximalInteger q) :
    strictInteger q ∣ N ∧ N ∣ maximalInteger q := by
  rcases hN with rfl | rfl
  · exact ⟨dvd_rfl, strict_dvd_weak hq⟩
  · exact ⟨strict_dvd_weak hq, dvd_rfl⟩

private theorem row01_log_nine_prime_floor : 22 < Real.log (5354228880 : ℝ) := by
  exact (rational_log_bounds 5354228880 (334639305 / 268435456)
    22 23 32 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])).1

private theorem row01_margin_of_eight_primes {n : ℕ} (hn : 5040 < n)
    (hcard : n.primeFactors.card ≤ 8) : 0 < robinLogMargin n := by
  have hr := D5.S3.Arith.Robin.FewDistinctPrimes.robin_of_card_primeFactors_le_eight hn hcard
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsR : (0 : ℝ) < (ArithmeticFunction.sigma 1 n : ℝ) :=
    Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n (by omega))
  have hloglog := Real.log_pos (log_gt_one (show 3 ≤ n by omega))
  have hlog := (Real.log_lt_iff_lt_exp (div_pos hsR hnR)).mpr
    (show (ArithmeticFunction.sigma 1 n : ℝ) / n <
        Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log (Real.log n))) by
      rw [Real.exp_add, Real.exp_log hloglog]
      exact hr)
  unfold robinLogMargin
  linarith only [hlog]

private theorem row01_endpoint_margin (q : ℝ) (hq : 0 < q) (hq0 : row01Price ≤ q)
    (N : ℕ) (hN : 5040 < N) (hend : N = strictInteger q ∨ N = maximalInteger q) :
    0 < robinLogMargin N := by
  have hd := endpoint_mem_divisibility_interval hq hend
  have hmax : maximalInteger q ∣ row01Integer := by
    rw [← row01_maximal_integer]
    exact weak_dvd_weak row01_price_pos hq hq0
  have hNdiv := hd.2.trans hmax
  by_cases hcard : N.primeFactors.card ≤ 8
  · exact row01_margin_of_eight_primes hN hcard
  have hsub : N.primeFactors ⊆ row01Primes := by
    rw [← row01_primeFactors]
    exact Nat.primeFactors_mono hNdiv (by norm_num [row01Integer])
  have hSupport : N.primeFactors = row01Primes :=
    Finset.eq_of_subset_of_card_le hsub (by rw [row01_prime_count]; omega)
  have hprod : 223092870 ∣ N := by
    have h := Nat.prod_primeFactors_dvd N
    rwa [hSupport, row01_prime_product] at h
  have hboundary : q < boundaryPrice := by
    by_contra! hle
    have hcap : maximalInteger q ∣ boundaryCap :=
      weak_dvd_weak boundaryPrice_spec.1 hq hle
    have hbad := hprod.trans (hd.2.trans hcap)
    rw [boundaryCap_eq_55440] at hbad
    exact (by decide : ¬ (223092870 : ℕ) ∣ 55440) hbad
  have hbase : 5040 ∣ N := by
    have hcap : boundaryCap ∣ strictInteger q :=
      weak_dvd_strict hq boundaryPrice_spec.1 hboundary
    rw [boundaryCap_eq_55440] at hcap
    exact (by decide : (5040 : ℕ) ∣ 55440).trans (hcap.trans hd.1)
  have hfloor : 5354228880 ∣ N := by
    have hlcm := Nat.lcm_dvd hbase hprod
    rwa [show Nat.lcm 5040 223092870 = 5354228880 by decide] at hlcm
  have hNlow : 5354228880 ≤ N := Nat.le_of_dvd (by omega) hfloor
  have hNhigh : N ≤ row01Integer :=
    Nat.le_of_dvd (by norm_num [row01Integer]) hNdiv
  have hlo : 22 ≤ Real.log (N : ℝ) := row01_log_nine_prime_floor.le.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hNlow))
  have hhi : Real.log (N : ℝ) ≤ 36 := by
    have h : Real.log (N : ℝ) ≤ Real.log (row01Integer : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hNhigh)
    exact h.trans (row01_log_height.2.le.trans (by norm_num))
  have hmargin := robin_log_margin_fixed_price_row01 hlo hhi
  have hopt := row01_optimal N (by omega)
  linarith only [hmargin, hopt]

/-- Unconditional strict Robin inequality through the exact Row 01 optimizer. -/
theorem original_robin_through_row01 {n : ℕ} (hn : 5040 < n) (hcap : n ≤ 321253732800) :
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  apply original_robin_through_maximal row01_price_pos row01_endpoint_margin hn
  rw [row01_maximal_integer]
  exact hcap

end

end D5.S3.Arith.Robin.Finite.RobinRow01
