/- GID: D5/S3/Arith/Robin/PriceRecord/ActualArbitraryBracketTwoTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualArbitraryBracketTwoTail
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Unconditional asymptotic full binary tails of original strict records. -/

import D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth

/-! The full tail uses natural truncated subtraction, including every equality
layer after the strict canonical cutoff. No Robin or RH conclusion is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail

open Real Filter
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.EulerLayerInventoryGrowth
open D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap

/-- The global case has zero gap. The non-global case uses the actual greatest
feasible optimizer and the original strict predecessor record. -/
private theorem finite_tail_gap {m : ℕ} (hm : 1 ≤ m) {c mu s : ℝ}
    (hc : 0 < c) (hmu : 0 < mu) (hs : 0 < s)
    (ha : optimalLayerCount c 2 ≤ m.factorization 2)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m)
    (hA : strictInteger s ≤ m) (hD : m ≤ maximalInteger s) :
    ∃ g : ℝ, 0 ≤ g ∧ s * g * exp g < 1 ∧
      h2 m c < g + 2 * (c / s) * log 2 := by
  obtain ⟨hn, _, _, hdelete⟩ := full_original2tail_deletion_identity hm ha s
  have hreward := (full_original2tail_reward_bound hc ha).2
  have hidentity := reward_deficit_identity m c
  by_cases hglobal : IsGoldenResourceOptimal s m
  · refine ⟨0, le_rfl, by simp, ?_⟩
    have hcomp := hglobal (deleted2tailInteger m c) hn
    have hbudget : s * h2 m c < 2 * c * log 2 := by linarith
    have hcancel : s * (2 * (c / s) * log 2) = 2 * c * log 2 := by
      field_simp
    have hlt : h2 m c < 2 * (c / s) * log 2 := by
      exact (mul_lt_mul_iff_right₀ hs).mp (by linarith only [hbudget, hcancel])
    simpa using hlt
  · obtain ⟨C, hgap⟩ := greatest_feasible_global_gap hs hA hD hglobal
    let g := log ((m : ℝ) / C)
    have hg : 0 < g := hgap.gap_pos
    have hstrict := hrecord C (by have := hgap.positive; omega) hgap.below
    have htransfer := objective_price_difference mu s hm hgap.positive
    have hupper : goldenResourceObjective s C - goldenResourceObjective s m <
        (s - mu) * g := by rw [htransfer]; dsimp only [g]; linarith
    have hnonneg := hgap.global m hm
    have hsmu : mu < s := by
      have hpos : 0 < (s - mu) * g := by linarith
      exact sub_pos.mp ((mul_pos_iff_of_pos_right hg).mp hpos)
    have hcomp := hgap.global (deleted2tailInteger m c) hn
    have hbudget : s * h2 m c < s * g + 2 * c * log 2 := by
      have hmg := mul_pos hmu hg
      nlinarith only [hcomp, hdelete, hupper, hidentity, hreward, hmg]
    refine ⟨g, hg.le, hgap.exponential_bound, ?_⟩
    apply (mul_lt_mul_iff_right₀ hs).mp
    have hcancel : s * (g + 2 * (c / s) * log 2) = s * g + 2 * c * log 2 := by
      field_simp
    linarith only [hbudget, hcancel]

/-- A one-sided estimate suffices, and only the lower canonical bracket is used.
The threshold precedes both the integer and every possible bracket price. -/
private theorem uniform_price_ratio {r : ℝ} (hr : 1 < r) :
    ∃ L : ℝ, 1 < L ∧ ∀ m : ℕ, L ≤ log (m : ℝ) →
      ∀ s : ℝ, 0 < s → strictInteger s ≤ m → ownPrice m / s ≤ r := by
  obtain ⟨α, hα, hαr⟩ := exists_between hr
  have hα0 : 0 < α := by linarith
  have hr0 : 0 < r := by linarith
  let ε := (α - 1) / (2 * α)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hεα : 1 < (1 - ε) * α := by
    dsimp only [ε]
    field_simp
    nlinarith
  obtain ⟨L₀, hL₀, hgrowth⟩ := strict_inventory_uniform_growth ε hε
  let B := α * log α / (r - α)
  refine ⟨max 2 (max (L₀ / α) (exp B)), by simp, ?_⟩
  intro m hm s hs hA
  let T := log (m : ℝ)
  have hT2 : 2 ≤ T := le_trans (le_max_left _ _) hm
  have hT : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < log T := log_pos hT
  have hTgrowth : L₀ / α ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hTexp : exp B ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have htL : L₀ ≤ α * T := by
    have hh := (div_le_iff₀ hα0).mp hTgrowth
    nlinarith only [hh]
  have ht : 1 < α * T := hL₀.trans_le htL
  have ht0 : 0 < α * T := by positivity
  have hq : 0 < price (α * T) :=
    one_div_pos.mpr (mul_pos ht0 (log_pos ht))
  let U := strictInteger (price (α * T))
  have hU : 0 < U := by have := strictInteger_pos hq; dsimp [U]; omega
  have hsize := hgrowth (α * T) htL U hU
    (fun p _ => strictInteger_counts hq p)
  have hlarge : T < log (U : ℝ) := by
    have hlo := (abs_lt.mp hsize).1
    have hquot : 1 - ε < log (U : ℝ) / (α * T) := by linarith
    have hmul := (lt_div_iff₀ ht0).mp hquot
    have hmain := mul_lt_mul_of_pos_right hεα hT0
    nlinarith only [hmul, hmain]
  have hB : B ≤ log T := by
    have hh := log_le_log (exp_pos B) hTexp
    simpa only [log_exp] using hh
  have hden : α * T * log (α * T) ≤ (T * log T) * r := by
    have hh : α * log α ≤ log T * (r - α) :=
      (div_le_iff₀ (sub_pos.mpr hαr)).mp hB
    have hhT := mul_le_mul_of_nonneg_right hh hT0.le
    rw [log_mul hα0.ne' hT0.ne']
    nlinarith only [hhT]
  have hprice : ownPrice m / r ≤ price (α * T) := by
    change (1 / (T * log T)) / r ≤ 1 / (α * T * log (α * T))
    rw [div_div]
    exact one_div_le_one_div_of_le (mul_pos ht0 (log_pos ht)) hden
  by_contra hnot
  have hratio : r < ownPrice m / s := lt_of_not_ge hnot
  have hsc : s < ownPrice m / r := by
    apply (lt_div_iff₀ hr0).mpr
    have hh := (lt_div_iff₀ hs).mp hratio
    nlinarith only [hh]
  have hdiv : U ∣ strictInteger s := strictInteger_dvd hq hs (hsc.trans_le hprice).le
  have hUm : U ≤ m := (Nat.le_of_dvd (by have := strictInteger_pos hs; omega) hdiv).trans hA
  have hlog : log (U : ℝ) ≤ log (m : ℝ) :=
    log_le_log (by exact_mod_cast hU) (by exact_mod_cast hUm)
  exact (not_lt_of_ge hlog) hlarge

private theorem gap_below_clock {r T s g : ℝ} (hr : 1 < r) (hT : 1 < T)
    (hs : 0 < s) (hg : 0 ≤ g)
    (hratio : (1 / (T * log T)) / s ≤ r)
    (hgap : s * g * exp g < 1) : g < log (r * T) := by
  have hr0 : 0 < r := by linarith
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < log T := log_pos hT
  have hden : 0 < T * log T := mul_pos hT0 hlogT
  have hcr : 1 / (T * log T) ≤ r * s := (div_le_iff₀ hs).mp hratio
  have hunit : 1 ≤ (r * s) * (T * log T) := (div_le_iff₀ hden).mp hcr
  by_contra hnot
  have hlg : log (r * T) ≤ g := le_of_not_gt hnot
  have hTle : T ≤ r * T := by nlinarith
  have hlogg : log T ≤ g := (log_le_log hT0 hTle).trans hlg
  have hexpg : r * T ≤ exp g := by
    have hh := exp_le_exp.mpr hlg
    simpa only [exp_log (mul_pos hr0 hT0)] using hh
  have hbound : 1 ≤ s * g * exp g := by
    calc
      1 ≤ s * log T * (r * T) := by nlinarith only [hunit]
      _ ≤ s * g * (r * T) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogg hs.le) (mul_pos hr0 hT0).le
      _ ≤ s * g * exp g := mul_le_mul_of_nonneg_left hexpg (mul_nonneg hs.le hg)
  linarith

/-- Every coefficient strictly greater than four bounds the full original binary
tail eventually, uniformly before the original integer and its positive price. -/
theorem full_original2tail_power_bound :
    ∀ K : ℝ, 4 < K → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ mu : ℝ, 0 < mu →
      (∀ n : ℕ, 0 < n → n < m →
        goldenResourceObjective mu n < goldenResourceObjective mu m) →
      (2 : ℝ) ^ (m.factorization 2 - optimalLayerCount (ownPrice m) 2) <
        K * log (m : ℝ) := by
  intro K hK
  have hfour : (1 : ℝ) * exp (2 * 1 * log 2) = 4 := by
    rw [show (2 : ℝ) * 1 * log 2 = log 2 + log 2 by ring, exp_add,
      exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hcontinuous : Continuous (fun r : ℝ => r * exp (2 * r * log 2)) := by fun_prop
  have hev : ∀ᶠ r : ℝ in 𝓝 1, r * exp (2 * r * log 2) < K :=
    (tendsto_order.mp hcontinuous.continuousAt).2 K (by
      change (1 : ℝ) * exp (2 * 1 * log 2) < K
      rwa [hfour])
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := hev.exists_Ioo_subset
  obtain ⟨r, hr, hru⟩ := exists_between hu
  have hrK : r * exp (2 * r * log 2) < K := hsub ⟨hl.trans hr, hru⟩
  have hr0 : 0 < r := by linarith
  obtain ⟨L, hL, hratio⟩ := uniform_price_ratio hr
  obtain ⟨N, hN⟩ := exists_nat_gt (exp L)
  refine ⟨max N 2, ?_⟩
  intro m hm mu hmu hrecord
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast (le_max_left N 2).trans hm
  have hLm : L < log (m : ℝ) := by
    have hh := log_lt_log (exp_pos L) (hN.trans_le hNm)
    simpa only [log_exp] using hh
  have hT : 1 < log (m : ℝ) := hL.trans hLm
  have hT0 : 0 < log (m : ℝ) := by linarith
  have hc : 0 < ownPrice m :=
    one_div_pos.mpr (mul_pos hT0 (log_pos hT))
  by_cases ha : optimalLayerCount (ownPrice m) 2 ≤ m.factorization 2
  · obtain ⟨s, hs, hA, hD⟩ := all_integer_bracketing m hm2
    have hrs := hratio m hLm.le s hs hA
    obtain ⟨g, hg, hgap, htail⟩ := finite_tail_gap hm1 hc hmu hs ha hrecord hA hD
    have hgclock := gap_below_clock hr hT hs hg hrs hgap
    have hcorrection : 2 * (ownPrice m / s) * log 2 ≤ 2 * r * log 2 := by
      have hh := mul_le_mul_of_nonneg_right hrs
        (show 0 ≤ 2 * log (2 : ℝ) by positivity)
      nlinarith only [hh]
    have hvolume : h2 m (ownPrice m) < log (r * log (m : ℝ)) + 2 * r * log 2 := by
      linarith
    have hpower : (2 : ℝ) ^ (m.factorization 2 - optimalLayerCount (ownPrice m) 2) =
        exp (h2 m (ownPrice m)) := by
      rw [← exp_log (pow_pos (by norm_num : (0 : ℝ) < 2)
        (m.factorization 2 - optimalLayerCount (ownPrice m) 2)), log_pow]
      rfl
    rw [hpower]
    calc
      _ < exp (log (r * log (m : ℝ)) + 2 * r * log 2) := exp_lt_exp.mpr hvolume
      _ = (r * exp (2 * r * log 2)) * log (m : ℝ) := by
        rw [exp_add, exp_log (mul_pos hr0 hT0)]
        ring
      _ < K * log (m : ℝ) := mul_lt_mul_of_pos_right hrK hT0
  · have hempty : m.factorization 2 - optimalLayerCount (ownPrice m) 2 = 0 := by omega
    rw [hempty, pow_zero]
    nlinarith

#print axioms full_original2tail_power_bound
#print axioms MediumPNT

end D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail
