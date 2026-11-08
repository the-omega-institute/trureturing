/- GID: D5/S3/Arith/Robin/PriceRecord/HalfSurplusFirstCell
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/HalfSurplusFirstCell
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Strict original half-surplus on the first continuum cell for every actual integer. -/

import D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
import D5.S3.Arith.Robin.PriceRecord.ActualInventorySmallPrimeBounds
import D5.S3.Arith.GoldenLocalThreshold
import D5.S3.Arith.GoldenResource.RobinRationalBasis

/-!
The first continuum cell of the original half-surplus inequality.
The integer, its actual valuations, the entire prime-power residual, and
the literal log-log curvature are retained. The scalar objective comparison
is applied separately to actual valuations, with no replacement of n.

The mathematical argument is the supplied first-cell derivation: the two,
three, and five directions have scalar minima at 4, 2, and 1, respectively.
The exact full-tail sum and positivity come from
FullPrimePowerArithmeticSurplus; the unbounded scalar comparison comes
from GoldenLocalThreshold. The atanh certificate uses RobinRationalBasis.
This is a bounded step toward the unchanged all-z>11 target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell

open Finset
open scoped BigOperators
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (tail layerTail)
open D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
open D5.S3.Arith.Robin.PriceRecord.ActualInventoryBounds
open D5.S3.Arith.GoldenResourceOptimalInteger (goldenLayerMarginal)
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResource.RobinRationalBasis

private theorem cell_log_bounds {z : ℝ} (hz : 11 < z) (hz13 : z ≤ 13) :
    239 / 100 < Real.log z ∧ Real.log z < 8 / 3 := by
  have hlo := (log_prime_11).1.trans
    (Real.log_lt_log (by norm_num : (0 : ℝ) < 11) hz)
  have hhi := (Real.log_le_log (by linarith : 0 < z) hz13).trans_lt
    (log_prime_13).2
  constructor <;> linarith only [hlo, hhi]

/-- Prices at the actual cutoff, including the closed endpoint thirteen. -/
private theorem cell_prices {z : ℝ} (hz : 11 < z) (hz13 : z ≤ 13) :
    (1 / 52 < Real.log 2 / (z * Real.log z) ∧
      Real.log 2 / (z * Real.log z) < 7 / 253) ∧
    (3 / 104 < Real.log 3 / (z * Real.log z) ∧
      Real.log 3 / (z * Real.log z) < 12 / 253) ∧
    (1 / 26 < Real.log 5 / (z * Real.log z) ∧
      Real.log 5 / (z * Real.log z) < 1 / 6) := by
  obtain ⟨hLlo, hLhi⟩ := cell_log_bounds hz hz13
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < Real.log z := by linarith
  have hD0 : 0 < z * Real.log z := mul_pos hz0 hL0
  have hDlo : 253 / 10 < z * Real.log z := by
    have hh := mul_lt_mul_of_pos_right hz hL0
    linarith only [hh, hLlo]
  have hDhi : z * Real.log z < 104 / 3 := by
    have hh := mul_le_mul_of_nonneg_right hz13 hL0.le
    linarith only [hh, hLhi]
  have h2 := log_prime_2
  have h3 := log_prime_3
  have h5 := log_prime_5
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply (lt_div_iff₀ hD0).mpr
    linarith only [hDhi, h2.1]
  · apply (div_lt_iff₀ hD0).mpr
    linarith only [hDlo, h2.2]
  · apply (lt_div_iff₀ hD0).mpr
    linarith only [hDhi, h3.1]
  · apply (div_lt_iff₀ hD0).mpr
    linarith only [hDlo, h3.2]
  · apply (lt_div_iff₀ hD0).mpr
    linarith only [hDhi, h5.1]
  · apply (div_lt_iff₀ hD0).mpr
    linarith only [hDlo, h5.2]

/-- Boundary conditions for the existing all-exponent scalar comparison.
The additional lower boundary at p=5 only permits use of the existing
comparison on all natural exponents; the actual exponent remains positive. -/
private theorem cell_thresholds {z : ℝ} (hz : 11 < z) (hz13 : z ≤ 13) :
    (goldenLayerMarginal 2 5 ≤ 1 / (z * Real.log z) ∧
      1 / (z * Real.log z) ≤ goldenLayerMarginal 2 4) ∧
    (goldenLayerMarginal 3 3 ≤ 1 / (z * Real.log z) ∧
      1 / (z * Real.log z) ≤ goldenLayerMarginal 3 2) ∧
    (goldenLayerMarginal 5 2 ≤ 1 / (z * Real.log z) ∧
      1 / (z * Real.log z) ≤ goldenLayerMarginal 5 1) := by
  obtain ⟨h2, h3, h5⟩ := cell_prices hz hz13
  have hlo31 : (1 / 31 : ℝ) ≤ Real.log (31 / 30) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 31 / 30)
    norm_num at h ⊢
    exact h
  have hlo13 : (1 / 13 : ℝ) ≤ Real.log (13 / 12) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 13 / 12)
    norm_num at h ⊢
    exact h
  have hlo6 : (1 / 6 : ℝ) ≤ Real.log (6 / 5) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 6 / 5)
    norm_num at h ⊢
    exact h
  have hhi63 : Real.log (63 / 62 : ℝ) < 1 / 62 := by
    have h := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 63 / 62) (by norm_num : (63 / 62 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hhi40 : Real.log (40 / 39 : ℝ) < 1 / 39 := by
    have h := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 40 / 39) (by norm_num : (40 / 39 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hhi31 : Real.log (31 / 30 : ℝ) < 1 / 30 := by
    have h := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 31 / 30) (by norm_num : (31 / 30 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hl5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · norm_num [goldenLayerMarginal]
    apply (div_le_iff₀ hl2).mpr
    have h : Real.log (63 / 62 : ℝ) ≤ Real.log 2 / (z * Real.log z) := by
      linarith only [hhi63, h2.1]
    simpa only [one_div, div_eq_mul_inv, mul_comm] using h
  · norm_num [goldenLayerMarginal]
    apply (le_div_iff₀ hl2).mpr
    have h : Real.log 2 / (z * Real.log z) ≤ Real.log (31 / 30 : ℝ) := by
      linarith only [hlo31, h2.2]
    simpa only [one_div, div_eq_mul_inv, mul_comm] using h
  · norm_num [goldenLayerMarginal]
    apply (div_le_iff₀ hl3).mpr
    have h : Real.log (40 / 39 : ℝ) ≤ Real.log 3 / (z * Real.log z) := by
      linarith only [hhi40, h3.1]
    simpa only [one_div, div_eq_mul_inv, mul_comm] using h
  · norm_num [goldenLayerMarginal]
    apply (le_div_iff₀ hl3).mpr
    have h : Real.log 3 / (z * Real.log z) ≤ Real.log (13 / 12 : ℝ) := by
      linarith only [hlo13, h3.2]
    simpa only [one_div, div_eq_mul_inv, mul_comm] using h
  · norm_num [goldenLayerMarginal]
    apply (div_le_iff₀ hl5).mpr
    have h : Real.log (31 / 30 : ℝ) ≤ Real.log 5 / (z * Real.log z) := by
      linarith only [hhi31, h5.1]
    simpa only [one_div, div_eq_mul_inv, mul_comm] using h
  · norm_num [goldenLayerMarginal]
    apply (le_div_iff₀ hl5).mpr
    have h : Real.log 5 / (z * Real.log z) ≤ Real.log (6 / 5 : ℝ) :=
      h5.2.le.trans hlo6
    simpa only [one_div, div_eq_mul_inv, mul_comm] using h

/-- Transfer the library's all-exponent objective comparison to the
actual signed contribution, leaving its entire reference tail intact. -/
private theorem contribution_comparison {z : ℝ} {n p a : ℕ} (hp : p.Prime)
    (hupper : goldenLayerMarginal p (a + 1) ≤ 1 / (z * Real.log z))
    (hlower : 1 / (z * Real.log z) ≤ goldenLayerMarginal p a) :
    -Real.log (1 - (p : ℝ)⁻¹ ^ (a + 1)) +
        ((a : ℝ) - (cutoffExponent z p : ℝ)) *
          (Real.log (p : ℝ) / (z * Real.log z)) -
        shiftedTail (p : ℝ)⁻¹ (cutoffExponent z p) ≤ primeContribution z n p := by
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hi1 : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hbase : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr hi1
  have hactual : 0 < 1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1) :=
    sub_pos.mpr (pow_lt_one₀ hi0.le hi1 (by omega))
  have hscalar : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ hi0.le hi1 (by omega))
  have h := golden_prime_local_objective_maximal_of_threshold hp
    (1 / (z * Real.log z)) hupper (Or.inr hlower) (n.factorization p)
  dsimp only [goldenPrimeLocalObjective] at h
  rw [Real.log_div hactual.ne' hbase.ne', Real.log_div hscalar.ne' hbase.ne'] at h
  dsimp only [primeContribution, layerTail]
  simp only [div_eq_mul_inv, one_mul] at h ⊢
  nlinarith only [h]

private theorem cell_cutoffs {z : ℝ} (hz : 11 < z) (hz13 : z ≤ 13) :
    cutoffExponent z 2 = 3 ∧ cutoffExponent z 3 = 2 ∧ cutoffExponent z 5 = 1 := by
  have h2 := (cutoff_spec (by linarith : 4 ≤ z) Nat.prime_two
    (by linarith : (2 : ℝ) ≤ z)).2.2.2
  have h3 := (cutoff_spec (by linarith : 4 ≤ z) Nat.prime_three
    (by linarith : (3 : ℝ) ≤ z)).2.2.2
  have h5 := (cutoff_spec (by linarith : 4 ≤ z) (by norm_num : Nat.Prime 5)
    (by linarith : (5 : ℝ) ≤ z)).2.2.2
  have hflo : 11 ≤ ⌊z⌋₊ := Nat.le_floor hz.le
  have hfhi : ⌊z⌋₊ ≤ 13 := by
    have hh := (Nat.floor_le (by linarith : 0 ≤ z)).trans hz13
    exact_mod_cast hh
  interval_cases hf : ⌊z⌋₊ <;> norm_num [hf, Nat.log] at h2 h3 h5 <;>
    exact ⟨h2, h3, h5⟩

/-- These are the full shifted infinite tails, obtained from the existing
summable prefix/residual equality, rather than from a finite tail cutoff. -/
private theorem cell_full_tails {z : ℝ} (hz : 11 < z) (hz13 : z ≤ 13) :
    shiftedTail (2 : ℝ)⁻¹ 3 = Real.log 2 - 2 / 3 ∧
    shiftedTail (3 : ℝ)⁻¹ 2 = Real.log (3 / 2) - 7 / 18 ∧
    shiftedTail (5 : ℝ)⁻¹ 1 = Real.log (5 / 4) - 1 / 5 := by
  obtain ⟨hb2, hb3, hb5⟩ := cell_cutoffs hz hz13
  have hz4 : 4 ≤ z := by linarith
  have h2 := prime_prefix_add_residual hz4 Nat.prime_two
    (by linarith : (2 : ℝ) ≤ z)
  have h3 := prime_prefix_add_residual hz4 Nat.prime_three
    (by linarith : (3 : ℝ) ≤ z)
  have h5 := prime_prefix_add_residual hz4 (by norm_num : Nat.Prime 5)
    (by linarith : (5 : ℝ) ≤ z)
  rw [residual_prime_eq_shift hz4 Nat.prime_two (by linarith : (2 : ℝ) ≤ z), hb2] at h2
  rw [residual_prime_eq_shift hz4 Nat.prime_three (by linarith : (3 : ℝ) ≤ z), hb3] at h3
  rw [residual_prime_eq_shift hz4 (by norm_num : Nat.Prime 5)
    (by linarith : (5 : ℝ) ≤ z), hb5] at h5
  have hi2 : -Real.log (1 - 1 / (2 : ℝ)) = Real.log 2 := by
    rw [show (1 - 1 / (2 : ℝ)) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hi3 : -Real.log (1 - 1 / (3 : ℝ)) = Real.log (3 / 2) := by
    rw [show (1 - 1 / (3 : ℝ)) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  have hi5 : -Real.log (1 - 1 / (5 : ℝ)) = Real.log (5 / 4) := by
    rw [show (1 - 1 / (5 : ℝ)) = (5 / 4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  rw [hi2] at h2
  rw [hi3] at h3
  rw [hi5] at h5
  norm_num [show Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide] at h2
  norm_num [show Icc 1 2 = ({1, 2} : Finset ℕ) by decide] at h3
  norm_num [show Icc 1 1 = ({1} : Finset ℕ) by decide] at h5
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [h2, h3, h5]

private theorem three_log_identity :
    Real.log (32 / 31 : ℝ) + Real.log (27 / 26 : ℝ) + Real.log (25 / 24 : ℝ) -
      Real.log 2 - Real.log (3 / 2 : ℝ) - Real.log (5 / 4 : ℝ) =
        Real.log (120 / 403 : ℝ) := by
  have hnum : Real.log ((32 / 31 : ℝ) * (27 / 26) * (25 / 24)) =
      Real.log (32 / 31 : ℝ) + Real.log (27 / 26 : ℝ) + Real.log (25 / 24 : ℝ) := by
    rw [Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have hden : Real.log ((2 : ℝ) * (3 / 2) * (5 / 4)) =
      Real.log 2 + Real.log (3 / 2 : ℝ) + Real.log (5 / 4 : ℝ) := by
    rw [Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have h := Real.log_div
    (by norm_num : ((32 / 31 : ℝ) * (27 / 26) * (25 / 24)) ≠ 0)
    (by norm_num : ((2 : ℝ) * (3 / 2) * (5 / 4)) ≠ 0)
  rw [hnum, hden] at h
  norm_num only [show ((32 / 31 : ℝ) * (27 / 26) * (25 / 24)) /
    ((2 : ℝ) * (3 / 2) * (5 / 4)) = 120 / 403 by norm_num] at h
  linarith only [h]

/-- An exact rational certificate using the existing general atanh remainder. -/
private theorem constant_lower :
    (21 / 500 : ℝ) < 113 / 90 + Real.log (120 / 403 : ℝ) := by
  have hs := atanh_remainder_sharp
    (by norm_num : (0 : ℝ) ≤ 283 / 523) (by norm_num : (283 / 523 : ℝ) < 1) 3
  rw [show ((1 + (283 / 523 : ℝ)) / (1 - (283 / 523 : ℝ))) = 403 / 120 by norm_num] at hs
  have hinv : Real.log (120 / 403 : ℝ) = -Real.log (403 / 120 : ℝ) := by
    rw [show (120 / 403 : ℝ) = (403 / 120 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hcert : (3470774833217983807 / 79477468742214794160 : ℝ) ≤
      113 / 90 + Real.log (120 / 403 : ℝ) := by
    rw [hinv]
    norm_num [atanhPartial, Finset.sum_range_succ] at hs
    linarith only [hs.2]
  exact (by norm_num : (21 / 500 : ℝ) <
    3470774833217983807 / 79477468742214794160).trans_le hcert

/-- The three directions bound the actual integer; every other prime
contribution, including thirteen at the endpoint, is paid by positivity. -/
private theorem actual_surplus_lower {z : ℝ} (hz : 11 < z) (hz13 : z ≤ 13)
    {n : ℕ} (hn : 0 < n) (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊) :
    21 / 500 + Real.log 2 / (z * Real.log z) <
      tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
        fullPrimePowerResidual z := by
  classical
  obtain ⟨ht2, ht3, ht5⟩ := cell_thresholds hz hz13
  obtain ⟨hb2, hb3, hb5⟩ := cell_cutoffs hz hz13
  obtain ⟨hr2, hr3, hr5⟩ := cell_full_tails hz hz13
  have hc2 := contribution_comparison (n := n) (a := 4) Nat.prime_two ht2.1 ht2.2
  have hc3 := contribution_comparison (n := n) (a := 2) Nat.prime_three ht3.1 ht3.2
  have hc5 := contribution_comparison (n := n) (a := 1) (by norm_num : Nat.Prime 5) ht5.1 ht5.2
  rw [hb2, hr2] at hc2
  rw [hb3, hr3] at hc3
  rw [hb5, hr5] at hc5
  have he2 : -Real.log (1 - (2 : ℝ)⁻¹ ^ (4 + 1)) = Real.log (32 / 31 : ℝ) := by
    rw [← Real.log_inv]
    norm_num
  have he3 : -Real.log (1 - (3 : ℝ)⁻¹ ^ (2 + 1)) = Real.log (27 / 26 : ℝ) := by
    rw [← Real.log_inv]
    norm_num
  have he5 : -Real.log (1 - (5 : ℝ)⁻¹ ^ (1 + 1)) = Real.log (25 / 24 : ℝ) := by
    rw [← Real.log_inv]
    norm_num
  rw [he2] at hc2
  rw [he3] at hc3
  rw [he5] at hc5
  norm_num only [Nat.cast_ofNat] at hc2 hc3 hc5
  have hthree : 113 / 90 + Real.log (120 / 403 : ℝ) +
      Real.log 2 / (z * Real.log z) ≤
      primeContribution z n 2 + primeContribution z n 3 + primeContribution z n 5 := by
    linarith only [hc2, hc3, hc5, three_log_identity]
  let S := Nat.primesLE ⌊z⌋₊
  let T : Finset ℕ := {2, 3, 5}
  have hTS : T ⊆ S := by
    intro p hp
    have hp' : p = 2 ∨ p = 3 ∨ p = 5 := by simpa only [T, mem_insert, mem_singleton] using hp
    rcases hp' with rfl | rfl | rfl
    all_goals apply Nat.mem_primesLE.mpr
    all_goals exact ⟨Nat.le_floor (by linarith), by norm_num⟩
  have hpos (p : ℕ) (hp : p ∈ S) : 0 < primeContribution z n p := by
    obtain ⟨hpf, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpz : (p : ℝ) ≤ z :=
      (by exact_mod_cast hpf : (p : ℝ) ≤ ⌊z⌋₊).trans
        (Nat.floor_le (by linarith : 0 ≤ z))
    have hpn : p ∈ n.primeFactors := by rw [hsupport]; exact hp
    exact prime_contribution_pos (by linarith : 4 ≤ z) hpp hpz
      (hpp.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hpn))
  have hsubset : (∑ p ∈ T, primeContribution z n p) ≤
      ∑ p ∈ S, primeContribution z n p :=
    sum_le_sum_of_subset_of_nonneg hTS (fun p hp _ => (hpos p hp).le)
  have hsum : 113 / 90 + Real.log (120 / 403 : ℝ) +
      Real.log 2 / (z * Real.log z) ≤ ∑ p ∈ S, primeContribution z n p := by
    apply hthree.trans
    simpa [T] using hsubset
  rw [full_surplus_eq_sum (by linarith : 4 ≤ z) hsupport]
  exact (add_lt_add_right constant_lower (Real.log 2 / (z * Real.log z))).trans_le hsum

/-- The unchanged strict half-surplus on the entire first continuum cell.
All original positive integers with literal full prime support and
0 < log(n)-z < 1/2 are quantified; there is no exponent cap. -/
theorem original_half_surplus_first_cell {z : ℝ} (hz : 11 < z) (hz13 : z ≤ 13)
    {n : ℕ} (hn : 0 < n)
    (hsupport : n.primeFactors = Nat.primesLE ⌊z⌋₊)
    (hM : 0 < Real.log (n : ℝ) - z)
    (hMhalf : Real.log (n : ℝ) - z < 1 / 2) :
    let A := tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
      fullPrimePowerResidual z
    let K := Real.log (Real.log z) + (Real.log (n : ℝ) - z) / (z * Real.log z) -
      Real.log (Real.log (Real.log (n : ℝ)))
    (1 / 2 : ℝ) < Real.sqrt z * Real.log z * (A - K) := by
  let A := tail n + (Real.log (n : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
    fullPrimePowerResidual z
  let K := Real.log (Real.log z) + (Real.log (n : ℝ) - z) / (z * Real.log z) -
    Real.log (Real.log (Real.log (n : ℝ)))
  let s := Real.sqrt z
  let L := Real.log z
  change (1 / 2 : ℝ) < s * L * (A - K)
  have hz0 : 0 < z := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hz0
  have hsq : s ^ 2 = z := Real.sq_sqrt hz0.le
  have hslo : 33 / 10 < s := by
    by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (by linarith only [hs0] : 0 ≤ 33 / 10 + s)
    nlinarith only [hz, hsq, hp]
  have hshi : s < 181 / 50 := by
    by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (by linarith only [hs0] : 0 ≤ s + 181 / 50)
    nlinarith only [hz13, hsq, hp]
  obtain ⟨hLlo, _⟩ := cell_log_bounds hz hz13
  change 239 / 100 < L at hLlo
  have hL0 : 0 < L := by linarith only [hLlo]
  have hA : 21 / 500 + Real.log 2 / (z * L) < A :=
    actual_surplus_lower hz hz13 hn hsupport
  have hAw := mul_lt_mul_of_pos_left hA (mul_pos hs0 hL0)
  have hAcancel : s * L * (21 / 500 + Real.log 2 / (z * L)) =
      s * L * (21 / 500) + Real.log 2 / s := by
    rw [← hsq]
    field_simp [hs0.ne', hL0.ne'] <;> ring
  rw [hAcancel] at hAw
  have hproduct : (33 / 10 : ℝ) * (239 / 100) < s * L := by
    exact (mul_lt_mul_of_pos_left hLlo (by norm_num : (0 : ℝ) < 33 / 10)).trans
      (mul_lt_mul_of_pos_right hslo hL0)
  have hratio : (69 / 362 : ℝ) < Real.log 2 / s := by
    apply (lt_div_iff₀ hs0).mpr
    have h := mul_lt_mul_of_pos_left hshi (by norm_num : (0 : ℝ) < 69 / 362)
    linarith only [h, (log_prime_2).1]
  have hAlower : (33 / 10 : ℝ) * (239 / 100) * (21 / 500) + 69 / 362 < s * L * A := by
    have h := mul_lt_mul_of_pos_right hproduct (by norm_num : (0 : ℝ) < 21 / 500)
    linarith only [h, hratio, hAw]
  have hclock : z + (Real.log (n : ℝ) - z) = Real.log (n : ℝ) := by ring
  have hkdata := arithmetic_surplus_dominates_loglog_curvature
    hz hM hMhalf hn hsupport
  dsimp only at hkdata
  rw [hclock] at hkdata
  have hK : K < (L + 1) / (8 * z ^ 2 * L ^ 2) := hkdata.2.1
  have hKw := mul_lt_mul_of_pos_left hK (mul_pos hs0 hL0)
  have hKcancel : s * L * ((L + 1) / (8 * z ^ 2 * L ^ 2)) =
      (L + 1) / (8 * z * s * L) := by
    rw [← hsq]
    field_simp [hs0.ne', hL0.ne'] <;> ring
  rw [hKcancel] at hKw
  have hKmid : (L + 1) / (8 * z * s * L) < 3 / (16 * z * s) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 8 * z * s * L)
      (by positivity : 0 < 16 * z * s)).mpr
    have h := mul_pos (by positivity : 0 < 8 * z * s) (by linarith : 0 < L - 2)
    nlinarith only [h]
  have hzs : (363 / 10 : ℝ) < z * s := by
    have h := mul_lt_mul_of_pos_right hz hs0
    linarith only [h, hslo]
  have hKend : (3 : ℝ) / (16 * z * s) < 5 / 968 := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 16 * z * s)
      (by norm_num : (0 : ℝ) < 968)).mpr
    linarith only [hzs]
  have hKupper : s * L * K < 5 / 968 := hKw.trans (hKmid.trans hKend)
  have hmargin : (33 / 10 : ℝ) * (239 / 100) * (21 / 500) + 69 / 362 - 5 / 968 =
      1 / 2 + 182834427 / 10950500000 := by norm_num
  rw [mul_sub]
  linarith only [hAlower, hKupper, hmargin]

end D5.S3.Arith.Robin.PriceRecord.HalfSurplusFirstCell
