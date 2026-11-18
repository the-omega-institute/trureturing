/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Counting
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Counting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entropy lower bounds from fixed finite prime bins with strict logarithmic slack. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
import D5.S3.Arith.Robin.Analytic.OmegaTail.Entropy
import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Counting
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open Selection Lower

/-- Any fixed family of interior bin densities of total mass one and strictly
negative logarithmic cost supplies its entropy as a lower counting exponent. -/
theorem finite_box_lower {J : Type*} [Fintype J] [DecidableEq J]
    (j0 : J) (a b r : J → ℝ) (lambda : ℝ)
    (ha : ∀ j, 0 < a j) (hab : ∀ j, a j < b j)
    (hdisj : Pairwise (fun i j => Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))))
    (hr : ∀ j, 0 < r j) (hroom : ∀ j, r j < b j - a j)
    (hsum : ∑ j, r j = 1) (hslack : lambda + ∑ j, r j * log (b j) < 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      (∑ j, (b j - a j) * binEntropy (r j / (b j - a j))) - epsilon ≤
        log (tailCount lambda x : ℝ) / scale x := by
  let P : J → ℝ → Finset ℕ := fun j x => primeInterval (a j * log x) (b j * log x)
  let k : J → ℝ → ℕ := adjustedSelection j0 r lambda
  have hP (j : J) : Tendsto (fun x : ℝ => ((P j x).card : ℝ) / scale x)
      atTop (𝓝 (b j - a j)) := primeInterval_capacity (ha j) (hab j)
  have hk := adjustedSelection_spec j0 r lambda (fun j => (hr j).le) (hr j0) hsum
  have hfit := adjustedSelection_fits j0 r (fun j => b j - a j) lambda
    (fun j x => (P j x).card) (fun j => (hr j).le) (hr j0) hsum hroom hP
  have hbudget := adjustedSelection_budget j0 r b lambda (fun j => (hr j).le)
    (hr j0) hsum (fun j => (ha j).trans (hab j)) hslack
  have hentropy := tendsto_finset_sum univ (fun j _ =>
    Entropy.log_choose_scaled scale (fun x => (P j x).card) (k j) scale_tendsto
      (sub_pos.mpr (hab j)) (hr j) (hroom j) (hP j) (hk.2 j))
  let E : ℝ := ∑ j, (b j - a j) * binEntropy (r j / (b j - a j))
  have hlow := hentropy.eventually_const_lt (show E - epsilon < E by dsimp [E]; linarith)
  filter_upwards [hfit, hk.1, hbudget, hlow, eventually_gt_atTop (exp 1)]
    with x hfitx hsumx hbudgetx hlowx hx
  have hL : 0 < log x := zero_lt_one.trans
    ((lt_log_iff_exp_lt ((exp_pos 1).trans hx)).mpr hx)
  have hy : 0 < scale x := scale_pos hx
  have hBx (j : J) : 0 < b j * log x := mul_pos ((ha j).trans (hab j)) hL
  have hprime (j : J) (p : ℕ) (hp : p ∈ P j x) : p.Prime := (mem_filter.mp hp).2
  have hcap (j : J) (p : ℕ) (hp : p ∈ P j x) : (p : ℝ) ≤ b j * log x :=
    (Nat.le_floor_iff (hBx j).le).mp (mem_Ioc.mp (mem_filter.mp hp).1).2
  have hdisjx : Pairwise (fun i j => Disjoint (P i x) (P j x)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro p hpi hpj
    have hmem (j : J) (hp : p ∈ P j x) : (p : ℝ) / log x ∈ Set.Ioc (a j) (b j) := by
      constructor
      · exact (lt_div_iff₀ hL).mpr (Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hp).1).1)
      · exact (div_le_iff₀ hL).mpr (hcap j p hp)
    exact Set.disjoint_left.mp (hdisj hij) (hmem i hpi) (hmem j hpj)
  have hcount : (∏ j, (P j x).card.choose (k j x)) ≤ tailCount lambda x := by
    apply multibox_bound (fun j => P j x) (fun j => k j x)
      (fun j => b j * log x) lambda x hdisjx hprime hBx hcap
    · rw [show (∑ j, k j x) = selectedCount lambda x from hsumx]
      simpa only [selectedCount, Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one (threshold lambda x)
    · exact hbudgetx.le
    · exact (exp_pos 1).trans hx
  have hchoose (j : J) : (0 : ℝ) < (P j x).card.choose (k j x) := by
    exact_mod_cast Nat.choose_pos (hfitx j)
  have hprod : (0 : ℝ) < ((∏ j, (P j x).card.choose (k j x) : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact prod_pos (fun j _ => hchoose j)
  have hlog : log ((∏ j, (P j x).card.choose (k j x) : ℕ) : ℝ) ≤
      log (tailCount lambda x : ℝ) := log_le_log hprod (by exact_mod_cast hcount)
  have hsplit : log ((∏ j, (P j x).card.choose (k j x) : ℕ) : ℝ) / scale x =
      ∑ j, log ((P j x).card.choose (k j x) : ℝ) / scale x := by
    rw [Nat.cast_prod, log_prod (fun j _ => (hchoose j).ne'), sum_div]
  have hbound := div_le_div_of_nonneg_right hlog hy.le
  rw [hsplit] at hbound
  exact hlowx.le.trans hbound

end D5.S3.Arith.Robin.Analytic.OmegaTail.Counting
