/- GID: D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Finite/EffectiveRobinTangentRows
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Two explicit strict-price optimizers and the original Row 01 cover every Robin height through 101. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Arith.Robin.Finite.RobinRow01

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows

open Finset
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.Robin.Finite.RobinRow01
open D5.S3.Weil.GronwallLowerEnvelope
open private layerRatio layer_ratio_eq_geometric golden_layer_marginal_antitone_base
  row01_log_height
  from D5.S3.Arith.Robin.Finite.RobinRow01

private theorem near_one_log_bounds (x lo hi : ℝ) (K : ℕ)
    (hx1 : 1 ≤ x) (hx2 : x < 2)
    (hcalc : lo < atanhPartial (atanhParameter x) K ∧
      atanhPartial (atanhParameter x) K +
        2 * atanhParameter x ^ (2*K+1) /
          ((2*K+1)*(1-atanhParameter x^2)) < hi) :
    lo < Real.log x ∧ Real.log x < hi := by
  have h := log_expansion_remainder_bound hx1 hx2 K
  unfold logRemainder at h
  constructor
  · linarith only [hcalc.1,h.1]
  · linarith only [hcalc.2,h.2]

private theorem layer_above {q : ℝ} (hq : 0 < q) {p k : ℕ} {r lo hi : ℝ}
    (hp : 1 < p) (hr : layerRatio p k = r)
    (hplog : Real.log (p : ℝ) < hi) (hrlog : lo < Real.log r)
    (hcalc : q * hi ≤ lo) : q < goldenLayerMarginal p k := by
  change q < Real.log (layerRatio p k) / Real.log p
  rw [hr, lt_div_iff₀ (Real.log_pos (by exact_mod_cast hp))]
  exact ((mul_le_mul_of_nonneg_left hplog.le hq.le).trans hcalc).trans_lt hrlog

private theorem layer_below {q : ℝ} (hq : 0 < q) {p k : ℕ} {r lo hi : ℝ}
    (hp : 1 < p) (hr : layerRatio p k = r)
    (hplog : lo < Real.log (p : ℝ)) (hrlog : Real.log r < hi)
    (hcalc : hi ≤ q * lo) : goldenLayerMarginal p k < q := by
  change Real.log (layerRatio p k) / Real.log p < q
  rw [hr, div_lt_iff₀ (Real.log_pos (by exact_mod_cast hp))]
  exact hrlog.trans_le (hcalc.trans (mul_le_mul_of_nonneg_left hplog.le hq.le))

private theorem factorization_roster (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (e : ℕ → ℕ) (p : ℕ) :
    (∏ r ∈ S, r ^ e r).factorization p = if p ∈ S then e p else 0 := by
  classical
  rw [Nat.factorization_prod_apply (fun r hr => pow_ne_zero _ (hS r hr).ne_zero)]
  have he (r : ℕ) (hr : r ∈ S) :
      (r ^ e r).factorization p = if r = p then e r else 0 := by
    simp [(hS r hr).factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_congr rfl he]
  simp [Finset.sum_ite_eq', eq_comm]

private theorem sigma_roster (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) :
    ArithmeticFunction.sigma 1 (∏ p ∈ S, p ^ e p) =
      ∏ p ∈ S, ∑ j ∈ Finset.range (e p + 1), p^j := by
  classical
  rw [ArithmeticFunction.IsMultiplicative.map_prod _ ArithmeticFunction.isMultiplicative_sigma]
  · apply Finset.prod_congr rfl
    intro p hp
    exact ArithmeticFunction.sigma_one_apply_prime_pow (hS p hp)
  · intro a ha b hb hab
    exact (((Nat.coprime_primes (hS a ha) (hS b hb)).mpr hab).pow_left _).pow_right _

/-- A genuine layer cutoff certificate suffices for full-domain optimality. -/
private theorem optimal_of_cuts {q : ℝ} (hq : 0 < q) {m : ℕ} (hm : 1 ≤ m)
    (K : ℕ) (cut : ℕ → ℕ)
    (hc2 : ∀ k, 1 ≤ k → k ≤ K → 2 ≤ cut k)
    (hcuts : ∀ k, 1 ≤ k → k ≤ K →
      q < goldenLayerMarginal (cut k) k ∧ goldenLayerMarginal (cut k+1) k < q)
    (hstop : goldenLayerMarginal 2 (K+1) < q)
    (hmax : ∀ p, p.Prime → m.factorization p ≤ K)
    (hmem : ∀ p k, p.Prime → 1 ≤ k → k ≤ K →
      (p ≤ cut k ↔ k ≤ m.factorization p)) :
    IsGoldenResourceOptimal q m := by
  apply (golden_resource_optimal_iff_layer_thresholds hq hm).mpr
  constructor
  · intro p hp
    let k := m.factorization p+1
    have hk : 1 ≤ k := by omega
    by_cases hkK : k ≤ K
    · have hpn : cut k+1 ≤ p := by
        by_contra! h
        have hh := (hmem p k hp hk hkK).mp (by omega)
        omega
      exact ((golden_layer_marginal_antitone_base (by linarith [hc2 k hk hkK]) hpn hk).trans_lt
        (hcuts k hk hkK).2).le
    · have hbase := (golden_layer_marginal_antitone_base (by norm_num) hp.two_le
        (by omega : 1 ≤ K+1)).trans_lt hstop
      have hKk : K+1 ≤ k := by omega
      rcases eq_or_lt_of_le hKk with he | he
      · change goldenLayerMarginal p k ≤ q
        rw [← he]
        exact hbase.le
      · exact ((golden_layer_strict_decrease hp (by omega : 1 ≤ K+1) he).trans hbase).le
  · intro p hp hd
    let k := m.factorization p
    have hk : 1 ≤ k := hp.factorization_pos_of_dvd (by omega : m ≠ 0) hd
    have hkK : k ≤ K := hmax p hp
    have hpk : p ≤ cut k := (hmem p k hp hk hkK).mpr le_rfl
    exact ((hcuts k hk hkK).1.trans_le
      (golden_layer_marginal_antitone_base hp.one_lt hpk hk)).le

/-- The exact support objective gives a positive margin across a real interval
of log heights once the same support line is positive at both endpoints. -/
private theorem fixed_price_interval {q L U : ℝ} {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hopt : IsGoldenResourceOptimal q m)
    (hL : 1 < L) (hLU : L < U)
    (hLn : L ≤ Real.log (n : ℝ)) (hnU : Real.log (n : ℝ) ≤ U)
    (hleft : 0 < robinThreshold L - q*L - goldenResourceObjective q m)
    (hright : 0 < robinThreshold U - q*U - goldenResourceObjective q m) :
    0 < robinLogMargin n := by
  let H := Real.log (n : ℝ)
  let t := (H-L)/(U-L)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hLn) (sub_nonneg.mpr hLU.le)
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hLU)).mpr (by linarith)
  have hH : (1-t)*L+t*U=H := by
    dsimp [t]
    field_simp [(sub_pos.mpr hLU).ne']
    <;> ring
  have hconc := threshold_strictConcaveOn.concaveOn.2
    (show L ∈ Set.Ioi (1:ℝ) from hL)
    (show U ∈ Set.Ioi (1:ℝ) from hL.trans hLU)
    (sub_nonneg.mpr ht1) ht0 (show (1-t)+t=1 by ring)
  simp only [smul_eq_mul,hH] at hconc
  let c := min (robinThreshold L - q*L - goldenResourceObjective q m)
    (robinThreshold U - q*U - goldenResourceObjective q m)
  have hc : 0 < c := lt_min hleft hright
  have hleft' := mul_le_mul_of_nonneg_left (min_le_left
    (robinThreshold L - q*L - goldenResourceObjective q m)
    (robinThreshold U - q*U - goldenResourceObjective q m)) (sub_nonneg.mpr ht1)
  have hright' := mul_le_mul_of_nonneg_left (min_le_right
    (robinThreshold L - q*L - goldenResourceObjective q m)
    (robinThreshold U - q*U - goldenResourceObjective q m)) ht0
  change (1-t)*c ≤ _ at hleft'
  change t*c ≤ _ at hright'
  have hlinear := congrArg (fun x : ℝ => q*x) hH
  have hG : 0 < robinThreshold H - q*H - goldenResourceObjective q m := by
    nlinarith only [hc,hleft',hright',hconc,hlinear]
  have hobj := hopt n hn
  have heq : robinLogMargin n = robinThreshold H - q*H - goldenResourceObjective q n := by
    rw [margin_eq_threshold_sub_W, golden_resource_sigma_identity q hn]
    unfold W H
    ring
  rw [heq]
  linarith only [hG,hobj]

def row02Price : ℝ := (9793 / 2000000)
def row02Integer : ℕ := 37188534050951960476800
private def row02Cut (k : ℕ) : ℕ := if k = 1 then 51 else if k = 2 then 9 else if k = 3 then 4 else if k = 4 then 3 else if k = 5 then 2 else if k = 6 then 2 else if k = 7 then 2 else 1
private def row02Exponent (p : ℕ) : ℕ := if p ≤ 2 then 7 else if p ≤ 3 then 4 else if p ≤ 4 then 3 else if p ≤ 9 then 2 else if p ≤ 51 then 1 else 0
private def row02Primes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47}

private theorem row02_price_pos : 0 < row02Price := by norm_num [row02Price]
private theorem row02_primes : ∀ p ∈ row02Primes, p.Prime := by decide
private theorem row02_primes_eq : row02Primes = Nat.primesLE 51 := by decide

private theorem row02_product :
    row02Integer = ∏ p ∈ row02Primes, p ^ row02Exponent p := by
  norm_num [row02Integer,row02Primes,row02Exponent,Finset.prod_insert]

private theorem row02_factorization (p : ℕ) (hp : p.Prime) :
    row02Integer.factorization p = row02Exponent p := by
  rw [row02_product, factorization_roster _ row02_primes, row02_primes_eq]
  by_cases h : p ≤ 51
  · rw [if_pos (Nat.mem_primesLE.mpr ⟨h,hp⟩)]
  · rw [if_neg (fun hmem => h (Nat.mem_primesLE.mp hmem).1)]
    unfold row02Exponent
    split_ifs <;> omega

private theorem row02_cut_member (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hK : k ≤ 7) :
    p ≤ row02Cut k ↔ k ≤ row02Integer.factorization p := by
  rw [row02_factorization p hp]
  have hp2 := hp.two_le
  interval_cases k <;> simp [row02Cut,row02Exponent] <;> split_ifs <;> omega

private theorem row02_cut_pos (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 7) :
    2 ≤ row02Cut k := by
  interval_cases k <;> norm_num [row02Cut]

private theorem row02_cut_signs (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 7) :
    row02Price < goldenLayerMarginal (row02Cut k) k ∧
      goldenLayerMarginal (row02Cut k+1) k < row02Price := by
  interval_cases k
  · constructor
    · change row02Price < goldenLayerMarginal 51 1
      have hpLog := rational_log_bounds 51 (51 / 32) (196591281 / 50000000) (78636513 / 20000000) 5 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (52 / 51) (1941807 / 100000000) (194181 / 10000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row02_price_pos (by norm_num)
        (r := (52 / 51)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row02Price])
    · change goldenLayerMarginal 52 1 < row02Price
      have hpLog := rational_log_bounds 52 (13 / 8) (39512437 / 10000000) (395124373 / 100000000) 5 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (53 / 52) (952409 / 50000000) (1904821 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row02_price_pos (by norm_num)
        (r := (53 / 52)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row02Price])
  · constructor
    · change row02Price < goldenLayerMarginal 9 2
      have hpLog := rational_log_bounds 9 (9 / 8) (27465307 / 12500000) (219722459 / 100000000) 3 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (91 / 90) (552491 / 50000000) (220997 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row02_price_pos (by norm_num)
        (r := (91 / 90)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row02Price])
    · change goldenLayerMarginal 10 2 < row02Price
      have hpLog := rational_log_bounds 10 (5 / 4) (57564627 / 25000000) (230258511 / 100000000) 3 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (111 / 110) (452491 / 50000000) (180997 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row02_price_pos (by norm_num)
        (r := (111 / 110)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row02Price])
  · constructor
    · change row02Price < goldenLayerMarginal 4 3
      have hpLog := rational_log_bounds 4 1 (27725887 / 20000000) (69314719 / 50000000) 2 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (85 / 84) (295861 / 25000000) (1183447 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row02_price_pos (by norm_num)
        (r := (85 / 84)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row02Price])
    · change goldenLayerMarginal 5 3 < row02Price
      have hpLog := rational_log_bounds 5 (5 / 4) (16094379 / 10000000) (160943793 / 100000000) 2 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (156 / 155) (40193 / 6250000) (643091 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row02_price_pos (by norm_num)
        (r := (156 / 155)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row02Price])
  · constructor
    · change row02Price < goldenLayerMarginal 3 4
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (121 / 120) (829879 / 100000000) (414941 / 50000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row02_price_pos (by norm_num)
        (r := (121 / 120)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row02Price])
    · change goldenLayerMarginal 4 4 < row02Price
      have hpLog := rational_log_bounds 4 1 (27725887 / 20000000) (69314719 / 50000000) 2 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (341 / 340) (73421 / 25000000) (293687 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row02_price_pos (by norm_num)
        (r := (341 / 340)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row02Price])
  · constructor
    · change row02Price < goldenLayerMarginal 2 5
      have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (63 / 62) (1600033 / 100000000) (400009 / 25000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row02_price_pos (by norm_num)
        (r := (63 / 62)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row02Price])
    · change goldenLayerMarginal 3 5 < row02Price
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (364 / 363) (137551 / 50000000) (55021 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row02_price_pos (by norm_num)
        (r := (364 / 363)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row02Price])
  · constructor
    · change row02Price < goldenLayerMarginal 2 6
      have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (127 / 126) (197629 / 25000000) (790519 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row02_price_pos (by norm_num)
        (r := (127 / 126)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row02Price])
    · change goldenLayerMarginal 3 6 < row02Price
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (1093 / 1092) (22883 / 25000000) (18307 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row02_price_pos (by norm_num)
        (r := (1093 / 1092)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row02Price])
  · constructor
    · change row02Price < goldenLayerMarginal 2 7
      have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (255 / 254) (196463 / 50000000) (392929 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row02_price_pos (by norm_num)
        (r := (255 / 254)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row02Price])
    · change goldenLayerMarginal 3 7 < row02Price
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (3280 / 3279) (30491 / 100000000) (15247 / 50000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row02_price_pos (by norm_num)
        (r := (3280 / 3279)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row02Price])

private theorem row02_stop : goldenLayerMarginal 2 8 < row02Price := by
  have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hrLog := near_one_log_bounds (511 / 510) (39177 / 20000000) (12243 / 6250000) 8
    (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
  exact layer_below row02_price_pos (by norm_num)
    (r := (511 / 510)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
    (by norm_num [row02Price])

theorem row02_optimal : IsGoldenResourceOptimal row02Price row02Integer := by
  apply optimal_of_cuts row02_price_pos (by norm_num [row02Integer]) 7 row02Cut
    row02_cut_pos row02_cut_signs row02_stop
  · intro p hp
    rw [row02_factorization p hp]
    unfold row02Exponent
    split_ifs <;> omega
  · exact row02_cut_member

private theorem row02_sigma : ArithmeticFunction.sigma 1 row02Integer = 256084420756786642944000 := by
  rw [row02_product, sigma_roster _ row02_primes]
  norm_num [row02Primes,row02Exponent,Finset.prod_insert,Finset.sum_range_succ]

private theorem row02_objective_upper :
    goldenResourceObjective row02Price row02Integer < (2093793 / 1250000) := by
  have hN := rational_log_bounds 37188534050951960476800 (290535422273062191225 / 147573952589676412928) (25985143 / 500000) (51970289 / 1000000) 74 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hA := rational_log_bounds (183060725760 / 26584046047) (45765181440 / 26584046047) (3859013 / 2000000) (4823767 / 2500000) 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  rw [golden_resource_sigma_identity _ (by norm_num [row02Integer]), row02_sigma]
  change Real.log (256084420756786642944000 / (37188534050951960476800 : ℝ)) - row02Price * Real.log (37188534050951960476800 : ℝ) < _
  have hmul := mul_le_mul_of_nonneg_left hN.1.le row02_price_pos.le
  unfold row02Price at *
  linarith only [hA.2,hmul]

private theorem row02_gap_left :
    0 < robinThreshold 36 - row02Price*36 -
      goldenResourceObjective row02Price row02Integer := by
  have hH := rational_log_bounds 36 (9 / 8) (3583517 / 1000000) (22397 / 6250) 5 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hLL := rational_log_bounds (3583517 / 1000000) (3583517 / 2000000) (6381723 / 5000000) (12763449 / 10000000) 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog := hLL.1.trans (Real.log_lt_log (by norm_num : (0 : ℝ) < (3583517 / 1000000)) hH.1)
  have hobj := row02_objective_upper
  unfold robinThreshold row02Price at *
  linarith only [eulerMascheroni_decimal_bounds.1,hlog,hobj]

private theorem row02_gap_right :
    0 < robinThreshold 70 - row02Price*70 -
      goldenResourceObjective row02Price row02Integer := by
  have hH := rational_log_bounds 70 (35 / 32) (2124247 / 500000) (4248497 / 1000000) 6 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hLL := rational_log_bounds (2124247 / 500000) (2124247 / 2000000) (3616411 / 2500000) (14465647 / 10000000) 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog := hLL.1.trans (Real.log_lt_log (by norm_num : (0 : ℝ) < (2124247 / 500000)) hH.1)
  have hobj := row02_objective_upper
  unfold robinThreshold row02Price at *
  linarith only [eulerMascheroni_decimal_bounds.1,hlog,hobj]

theorem row02_margin {n : ℕ} (hn : 1 ≤ n)
    (hL : 36 ≤ Real.log (n : ℝ)) (hU : Real.log (n : ℝ) ≤ 70) :
    0 < robinLogMargin n :=
  fixed_price_interval (by norm_num [row02Integer]) hn row02_optimal
    (by norm_num) (by norm_num) hL hU row02_gap_left row02_gap_right

def row03Price : ℝ := (54619 / 25000000)
def row03Integer : ℕ := 46015447651610234928592313897306120347488000
private def row03Cut (k : ℕ) : ℕ := if k = 1 then 99 else if k = 2 then 12 else if k = 3 then 5 else if k = 4 then 3 else if k = 5 then 3 else if k = 6 then 2 else if k = 7 then 2 else if k = 8 then 2 else 1
private def row03Exponent (p : ℕ) : ℕ := if p ≤ 2 then 8 else if p ≤ 3 then 5 else if p ≤ 5 then 3 else if p ≤ 12 then 2 else if p ≤ 99 then 1 else 0
private def row03Primes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}

private theorem row03_price_pos : 0 < row03Price := by norm_num [row03Price]
private theorem row03_primes : ∀ p ∈ row03Primes, p.Prime := by decide
private theorem row03_primes_eq : row03Primes = Nat.primesLE 99 := by decide

private theorem row03_product :
    row03Integer = ∏ p ∈ row03Primes, p ^ row03Exponent p := by
  norm_num [row03Integer,row03Primes,row03Exponent,Finset.prod_insert]

private theorem row03_factorization (p : ℕ) (hp : p.Prime) :
    row03Integer.factorization p = row03Exponent p := by
  rw [row03_product, factorization_roster _ row03_primes, row03_primes_eq]
  by_cases h : p ≤ 99
  · rw [if_pos (Nat.mem_primesLE.mpr ⟨h,hp⟩)]
  · rw [if_neg (fun hmem => h (Nat.mem_primesLE.mp hmem).1)]
    unfold row03Exponent
    split_ifs <;> omega

private theorem row03_cut_member (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hK : k ≤ 8) :
    p ≤ row03Cut k ↔ k ≤ row03Integer.factorization p := by
  rw [row03_factorization p hp]
  have hp2 := hp.two_le
  interval_cases k <;> simp [row03Cut,row03Exponent] <;> split_ifs <;> omega

private theorem row03_cut_pos (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 8) :
    2 ≤ row03Cut k := by
  interval_cases k <;> norm_num [row03Cut]

private theorem row03_cut_signs (k : ℕ) (hk : 1 ≤ k) (hK : k ≤ 8) :
    row03Price < goldenLayerMarginal (row03Cut k) k ∧
      goldenLayerMarginal (row03Cut k+1) k < row03Price := by
  interval_cases k
  · constructor
    · change row03Price < goldenLayerMarginal 99 1
      have hpLog := rational_log_bounds 99 (99 / 64) (459511983 / 100000000) (459511987 / 100000000) 6 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (100 / 99) (125629 / 12500000) (201007 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (100 / 99)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 100 1 < row03Price
      have hpLog := rational_log_bounds 100 (25 / 16) (460517017 / 100000000) (23025851 / 5000000) 6 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (101 / 100) (124379 / 12500000) (199007 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (101 / 100)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])
  · constructor
    · change row03Price < goldenLayerMarginal 12 2
      have hpLog := rational_log_bounds 12 (3 / 2) (248490663 / 100000000) (248490667 / 100000000) 3 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (157 / 156) (319489 / 50000000) (638981 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (157 / 156)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 13 2 < row03Price
      have hpLog := rational_log_bounds 13 (13 / 8) (128247467 / 50000000) (256494937 / 100000000) 3 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (183 / 182) (109589 / 20000000) (136987 / 25000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (183 / 182)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])
  · constructor
    · change row03Price < goldenLayerMarginal 5 3
      have hpLog := rational_log_bounds 5 (5 / 4) (16094379 / 10000000) (160943793 / 100000000) 2 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (156 / 155) (40193 / 6250000) (643091 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (156 / 155)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 6 3 < row03Price
      have hpLog := rational_log_bounds 6 (3 / 2) (35835189 / 20000000) (44793987 / 25000000) 2 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (259 / 258) (193423 / 50000000) (386849 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (259 / 258)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])
  · constructor
    · change row03Price < goldenLayerMarginal 3 4
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (121 / 120) (829879 / 100000000) (414941 / 50000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (121 / 120)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 4 4 < row03Price
      have hpLog := rational_log_bounds 4 1 (27725887 / 20000000) (69314719 / 50000000) 2 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (341 / 340) (73421 / 25000000) (293687 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (341 / 340)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])
  · constructor
    · change row03Price < goldenLayerMarginal 3 5
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (364 / 363) (137551 / 50000000) (55021 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (364 / 363)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 4 5 < row03Price
      have hpLog := rational_log_bounds 4 1 (27725887 / 20000000) (69314719 / 50000000) 2 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (1365 / 1364) (14657 / 20000000) (9161 / 12500000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (1365 / 1364)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])
  · constructor
    · change row03Price < goldenLayerMarginal 2 6
      have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (127 / 126) (197629 / 25000000) (790519 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (127 / 126)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 3 6 < row03Price
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (1093 / 1092) (22883 / 25000000) (18307 / 20000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (1093 / 1092)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])
  · constructor
    · change row03Price < goldenLayerMarginal 2 7
      have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (255 / 254) (196463 / 50000000) (392929 / 100000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (255 / 254)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 3 7 < row03Price
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (3280 / 3279) (30491 / 100000000) (15247 / 50000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (3280 / 3279)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])
  · constructor
    · change row03Price < goldenLayerMarginal 2 8
      have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (511 / 510) (39177 / 20000000) (12243 / 6250000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_above row03_price_pos (by norm_num)
        (r := (511 / 510)) (by norm_num [layerRatio]) hpLog.2 hrLog.1
        (by norm_num [row03Price])
    · change goldenLayerMarginal 3 8 < row03Price
      have hpLog := rational_log_bounds 3 (3 / 2) (109861227 / 100000000) (10986123 / 10000000) 1 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, Finset.sum_range_succ])
      have hrLog := near_one_log_bounds (9841 / 9840) (10161 / 100000000) (2541 / 25000000) 8
        (by norm_num) (by norm_num)
        (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
      exact layer_below row03_price_pos (by norm_num)
        (r := (9841 / 9840)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
        (by norm_num [row03Price])

private theorem row03_stop : goldenLayerMarginal 2 9 < row03Price := by
  have hpLog := rational_log_bounds 2 1 (69314717 / 100000000) (433217 / 625000) 1 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hrLog := near_one_log_bounds (1023 / 1022) (48899 / 50000000) (97801 / 100000000) 8
    (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, atanhParameter, Finset.sum_range_succ])
  exact layer_below row03_price_pos (by norm_num)
    (r := (1023 / 1022)) (by norm_num [layerRatio]) hpLog.1 hrLog.2
    (by norm_num [row03Price])

theorem row03_optimal : IsGoldenResourceOptimal row03Price row03Integer := by
  apply optimal_of_cuts row03_price_pos (by norm_num [row03Integer]) 8 row03Cut
    row03_cut_pos row03_cut_signs row03_stop
  · intro p hp
    rw [row03_factorization p hp]
    unfold row03Exponent
    split_ifs <;> omega
  · exact row03_cut_member

private theorem row03_sigma : ArithmeticFunction.sigma 1 row03Integer = 371416230138979938642326701195548583526400000 := by
  rw [row03_product, sigma_roster _ row03_primes]
  norm_num [row03Primes,row03Exponent,Finset.prod_insert,Finset.sum_range_succ]

private theorem row03_objective_upper :
    goldenResourceObjective row03Price row03Integer < (233587 / 125000) := by
  have hN := rational_log_bounds 46015447651610234928592313897306120347488000 (179747842389102480189813726161352032607375 / 174224571863520493293247799005065324265472) (2010751 / 20000) (100537553 / 1000000) 145 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hA := rational_log_bounds (252048262429789777192550400 / 31226728086646675228170943) (31506032803723722149068800 / 31226728086646675228170943) (1044173 / 500000) (20883463 / 10000000) 3 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  rw [golden_resource_sigma_identity _ (by norm_num [row03Integer]), row03_sigma]
  change Real.log (371416230138979938642326701195548583526400000 / (46015447651610234928592313897306120347488000 : ℝ)) - row03Price * Real.log (46015447651610234928592313897306120347488000 : ℝ) < _
  have hmul := mul_le_mul_of_nonneg_left hN.1.le row03_price_pos.le
  unfold row03Price at *
  linarith only [hA.2,hmul]

private theorem row03_gap_left :
    0 < robinThreshold 70 - row03Price*70 -
      goldenResourceObjective row03Price row03Integer := by
  have hH := rational_log_bounds 70 (35 / 32) (2124247 / 500000) (4248497 / 1000000) 6 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hLL := rational_log_bounds (2124247 / 500000) (2124247 / 2000000) (3616411 / 2500000) (14465647 / 10000000) 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog := hLL.1.trans (Real.log_lt_log (by norm_num : (0 : ℝ) < (2124247 / 500000)) hH.1)
  have hobj := row03_objective_upper
  unfold robinThreshold row03Price at *
  linarith only [eulerMascheroni_decimal_bounds.1,hlog,hobj]

private theorem row03_gap_right :
    0 < robinThreshold 101 - row03Price*101 -
      goldenResourceObjective row03Price row03Integer := by
  have hH := rational_log_bounds 101 (101 / 64) (4615119 / 1000000) (2307561 / 500000) 6 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hLL := rational_log_bounds (4615119 / 1000000) (4615119 / 4000000) (122347 / 80000) (7646689 / 5000000) 2 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hlog := hLL.1.trans (Real.log_lt_log (by norm_num : (0 : ℝ) < (4615119 / 1000000)) hH.1)
  have hobj := row03_objective_upper
  unfold robinThreshold row03Price at *
  linarith only [eulerMascheroni_decimal_bounds.1,hlog,hobj]

theorem row03_margin {n : ℕ} (hn : 1 ≤ n)
    (hL : 70 ≤ Real.log (n : ℝ)) (hU : Real.log (n : ℝ) ≤ 101) :
    0 < robinLogMargin n :=
  fixed_price_interval (by norm_num [row03Integer]) hn row03_optimal
    (by norm_num) (by norm_num) hL hU row03_gap_left row03_gap_right

/-- The original Row 01 and both new rows establish the entire finite height bridge. -/
theorem robin_margin_through_height_101 {n : ℕ} (hn : 5040 < n)
    (hH : Real.log (n : ℝ) ≤ 101) : 0 < robinLogMargin n := by
  by_cases hsmall : n ≤ row01Integer
  · have hR := original_robin_through_row01 hn (by simpa [row01Integer] using hsmall)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog := D5.S3.Arith.Robin.PaddingRatio.loglog_pos (by omega : 5041 ≤ n)
    have hden : 0 < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) :=
      mul_pos (mul_pos (Real.exp_pos _) hnR) hlog
    have hratio : D5.S3.Arith.Robin.PaddingRatio.robinRatio n < 1 :=
      (div_lt_one hden).mpr hR
    have hpos : 0 < D5.S3.Arith.Robin.PaddingRatio.robinRatio n :=
      div_pos (Nat.cast_pos.mpr (ArithmeticFunction.sigma_pos 1 n (by omega))) hden
    rw [robin_log_margin_eq_neg_log (by omega : 5041 ≤ n)]
    exact neg_pos.mpr (Real.log_neg hpos hratio)
  have hN : (row01Integer : ℝ) ≤ n := by exact_mod_cast (le_of_lt (lt_of_not_ge hsmall))
  have hheight := row01_log_height.1.trans_le
    (Real.log_le_log (by norm_num [row01Integer]) hN)
  have h22 : 22 ≤ Real.log (n : ℝ) := by linarith
  by_cases h36 : Real.log (n : ℝ) ≤ 36
  · have hr := robin_log_margin_fixed_price_row01 h22 h36
    have ho := (row01_optimal_iff (m := row01Integer) (by norm_num [row01Integer])).mpr rfl
    have hobj := ho n (by omega)
    linarith only [hr,hobj]
  · by_cases h70 : Real.log (n : ℝ) ≤ 70
    · exact row02_margin (by omega) (le_of_lt (lt_of_not_ge h36)) h70
    · exact row03_margin (by omega) (le_of_lt (lt_of_not_ge h70)) hH

end D5.S3.Arith.Robin.Finite.EffectiveRobinTangentRows
