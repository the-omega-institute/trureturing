/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.Probability.Quantile
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Midpoint Riemann sums via the quantile function

For a probability measure `μ` on `ℝ` and a bounded continuous test function `φ : ℝ → ℝ`, the
**midpoint Riemann sums** of `φ ∘ quantile μ` on `[0, 1]` converge to `∫ φ dμ`:

```
(1 / (n + 1)) * ∑ k : Fin (n + 1), φ (quantile μ ((k + 1/2) / (n + 1))) → ∫ φ dμ.
```

These sums are the integrals over `Ioo 0 1` of the step functions `stepFun μ φ n`, which are
constant `φ (quantile μ ((k + 1/2)/n))` on each bin `[k/n, (k+1)/n)` of the uniform partition.

## Main definitions

* `Measure.binMidpoint` — the bin-midpoint map `t ↦ (⌊n·t⌋₊ + 1/2) / n`.
* `Measure.stepFun` — the step function `t ↦ φ (quantile μ (binMidpoint n t))`.

## Main statements

* `Measure.tendsto_integral_of_quantile_midpoint` — the midpoint sums converge to `∫ φ dμ`.

## Tags

quantile, riemann sum, midpoint rule, dominated convergence
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace MeasureTheory.Measure

variable {μ : Measure ℝ}

/-! ### The midpoint partition

For `n : ℕ` with `n ≥ 1`, the function `midpoint n t = (⌊n t⌋₊ + 1/2) / n` sends
`t ∈ [k/n, (k+1)/n)` to `(k + 1/2) / n`, i.e. the midpoint of the `k`-th bin of the uniform
partition of `[0, 1]` into `n` subintervals. -/

/-- The midpoint function for the uniform partition of size `n`. -/
def binMidpoint (n : ℕ) (t : ℝ) : ℝ := ((⌊(n : ℝ) * t⌋₊ : ℝ) + 1 / 2) / n

/-- On `[0, 1)`, the midpoint is within `1/n` of `t`. -/
-- `_ht1` unused: the bound only needs the floor sandwich, not `t < 1`; kept to match
-- `binMidpoint_mem_Ioo`'s hypotheses.
lemma abs_binMidpoint_sub_le {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (_ht1 : t < 1) :
    |binMidpoint n t - t| ≤ 1 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  set y : ℝ := (n : ℝ) * t with hy_def
  have hy0 : 0 ≤ y := mul_nonneg hnpos.le ht0
  -- `⌊y⌋₊ ≤ y < ⌊y⌋₊ + 1`.
  have hfl_le : ((⌊y⌋₊ : ℝ)) ≤ y := Nat.floor_le hy0
  have hlt_fl : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  -- binMidpoint n t - t = (⌊y⌋₊ + 1/2)/n - y/n = (⌊y⌋₊ + 1/2 - y)/n.
  have h_expand : binMidpoint n t - t = (((⌊y⌋₊ : ℝ) + 1 / 2) - y) / n := by
    unfold binMidpoint
    rw [hy_def]
    field_simp
  rw [h_expand, abs_div, abs_of_pos hnpos]
  have habs : |((⌊y⌋₊ : ℝ)) + 1 / 2 - y| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  gcongr

/-- On `[0, 1)`, the midpoint lands in `Ioo 0 1`. -/
lemma binMidpoint_mem_Ioo {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    binMidpoint n t ∈ Ioo (0 : ℝ) 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  set y : ℝ := (n : ℝ) * t with hy_def
  have hy0 : 0 ≤ y := mul_nonneg hnpos.le ht0
  -- `⌊y⌋₊ ≤ y < ⌊y⌋₊ + 1`.
  have hfl_le : ((⌊y⌋₊ : ℝ)) ≤ y := Nat.floor_le hy0
  have hlt_fl : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  -- `⌊y⌋₊ ≤ y = n·t < n·1 = n`, so `⌊y⌋₊ ≤ n - 1`.
  have h_y_lt : y < n := by
    rw [hy_def]
    calc (n : ℝ) * t < n * 1 := by nlinarith
      _ = n := by ring
  have hfl_lt_n : (⌊y⌋₊ : ℝ) < n := by linarith
  have hfl_nat_lt : ⌊y⌋₊ < n := by exact_mod_cast hfl_lt_n
  refine ⟨?_, ?_⟩
  · -- `(⌊y⌋₊ + 1/2) / n > 0`.
    apply div_pos
    · have : (0 : ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_nonneg _
      linarith
    · exact hnpos
  · -- `(⌊y⌋₊ + 1/2) / n < 1` iff `⌊y⌋₊ + 1/2 < n`.
    unfold binMidpoint
    rw [div_lt_one hnpos]
    -- Since `⌊y⌋₊ + 1 ≤ n`, we have `⌊y⌋₊ + 1/2 ≤ n - 1/2 < n`.
    have hfl_add_one : ((⌊y⌋₊ : ℝ)) + 1 ≤ n := by exact_mod_cast hfl_nat_lt
    linarith

/-- `binMidpoint` is constant on each bin `Ico (k/n) ((k+1)/n)` with `k : Fin n`. On that bin, its
value is `(k + 1/2) / n`. -/
lemma binMidpoint_eq_of_mem_Ico {n : ℕ} (hn : 1 ≤ n) (k : Fin n) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    binMidpoint n t = ((k : ℝ) + 1 / 2) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  obtain ⟨ht_le, ht_lt⟩ := ht
  -- `k/n ≤ t < (k+1)/n` means `k ≤ n·t < k+1`, so `⌊n·t⌋₊ = k`.
  have h_nt_ge : (k : ℝ) ≤ n * t := by
    have := (div_le_iff₀ hnpos).mp ht_le
    linarith
  have h_nt_lt : n * t < (k : ℝ) + 1 := by
    have := (lt_div_iff₀ hnpos).mp ht_lt
    linarith
  have h_nt_nn : 0 ≤ (n : ℝ) * t := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have h_floor_eq : ⌊(n : ℝ) * t⌋₊ = k := by
    rw [Nat.floor_eq_iff h_nt_nn]
    refine ⟨?_, ?_⟩
    · exact h_nt_ge
    · linarith
  unfold binMidpoint
  rw [h_floor_eq]

/-- The bins `Ico (k/n) ((k+1)/n)` for `k : Fin n` are pairwise disjoint. -/
lemma bins_pairwise_disjoint (n : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun (k : Fin n) => Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))) := by
  -- Prove the symmetric version first.
  have h_aux : ∀ (i j : Fin n), i < j →
      Disjoint (Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n))
        (Ico ((j : ℝ) / n) (((j : ℝ) + 1) / n)) := by
    intro i j hlt
    by_cases hn : 1 ≤ n
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have h_ij : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
      refine Set.disjoint_iff.mpr fun t ht => ?_
      simp only [Set.mem_inter_iff, Set.mem_Ico] at ht
      have h1 : t < ((i : ℝ) + 1) / n := ht.1.2
      have h2 : ((j : ℝ) : ℝ) / n ≤ t := ht.2.1
      have h3 : ((i : ℝ) + 1) / n ≤ ((j : ℝ)) / n :=
        div_le_div_of_nonneg_right h_ij hnpos.le
      linarith
    · push Not at hn
      interval_cases n
      exact i.elim0
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact h_aux i j hlt
  · exact (h_aux j i hgt).symm

/-- The union of bins `Ico (k/n) ((k+1)/n)` for `k : Fin n` equals `Ico 0 1`. -/
lemma iUnion_bins_eq_Ico (n : ℕ) (hn : 1 ≤ n) :
    ⋃ (k : Fin n), Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n) = Ico (0 : ℝ) 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  ext t
  simp only [Set.mem_iUnion, Set.mem_Ico]
  constructor
  · rintro ⟨k, hk_le, hk_lt⟩
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ (k : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hnpos.le
      linarith
    · have h_k1_le : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast k.2
      have h_bound : ((k : ℝ) + 1) / n ≤ 1 := (div_le_one hnpos).mpr h_k1_le
      linarith
  · rintro ⟨ht0, ht1⟩
    -- Take `k = ⌊n * t⌋₊`, which is `< n` since `n*t < n`.
    have h_nt_nn : 0 ≤ (n : ℝ) * t := mul_nonneg hnpos.le ht0
    have h_nt_lt : (n : ℝ) * t < n := by nlinarith
    have h_floor_lt : ⌊(n : ℝ) * t⌋₊ < n := by
      rw [Nat.floor_lt h_nt_nn]; exact h_nt_lt
    refine ⟨⟨⌊(n : ℝ) * t⌋₊, h_floor_lt⟩, ?_, ?_⟩
    · simp only
      rw [div_le_iff₀ hnpos]
      have := Nat.floor_le h_nt_nn
      linarith
    · simp only
      rw [lt_div_iff₀ hnpos]
      have := Nat.lt_floor_add_one ((n : ℝ) * t)
      linarith

/-! ### The step function approximation -/

/-- Step function: `stepFun μ φ n t = φ (quantile μ (binMidpoint n t))`. -/
def stepFun (μ : Measure ℝ) (φ : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  φ (quantile μ (binMidpoint n t))

/-- On each bin, `stepFun` is the constant `φ (quantile μ ((k + 1/2) / n))`. -/
lemma stepFun_eq_of_mem_Ico {μ : Measure ℝ} {φ : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n) (k : Fin n)
    {t : ℝ} (ht : t ∈ Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    stepFun μ φ n t = φ (quantile μ (((k : ℝ) + 1 / 2) / n)) := by
  unfold stepFun
  rw [binMidpoint_eq_of_mem_Ico hn k ht]

/-- The step function is bounded by `M` whenever `|φ| ≤ M`. -/
lemma abs_stepFun_le {μ : Measure ℝ} {φ : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |φ x| ≤ M)
    (n : ℕ) (t : ℝ) : |stepFun μ φ n t| ≤ M := by
  unfold stepFun
  exact hM _

/-! ### Integral of the step function on `Ioo 0 1` equals the midpoint sum -/

/-- Measurability: `binMidpoint n` is measurable. -/
lemma measurable_binMidpoint (n : ℕ) : Measurable (binMidpoint n) := by
  unfold binMidpoint
  -- `(⌊n · t⌋₊ : ℝ) + 1/2) / n` is measurable as a composition of measurable functions.
  refine Measurable.div_const ?_ _
  refine Measurable.add_const ?_ _
  -- `⌊n · t⌋₊ : ℕ → ℝ`, the natural-cast.
  have h1 : Measurable fun t : ℝ => ⌊(n : ℝ) * t⌋₊ := by
    exact Nat.measurable_floor.comp (measurable_const.mul measurable_id)
  -- Any function from `ℕ` (discrete measurable space) to `ℝ` is measurable.
  have h2 : Measurable ((↑) : ℕ → ℝ) := fun _ _ => trivial
  exact h2.comp h1

/-- The step function is AE-strongly-measurable on `Ioo 0 1`, for continuous `φ`. -/
-- `_hφ` unused: `stepFun` is a finite sum of indicators of constants, measurable regardless of
-- `φ`'s continuity; kept so the hypothesis matches `integral_stepFun_Ioo`.
lemma aestronglyMeasurable_stepFun {φ : ℝ → ℝ} (_hφ : Continuous φ) (n : ℕ) :
    AEStronglyMeasurable (stepFun μ φ n) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  by_cases hn : 1 ≤ n
  · -- On Ico 0 1, stepFun equals ∑ k ∈ Finset.univ, indicator of k-th bin times v_k.
    -- This is strongly measurable as a finite sum of indicators of measurable sets.
    set g : ℝ → ℝ := (fun t => ∑ k : Fin n,
      (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)).indicator
        (fun _ : ℝ => φ (quantile μ (((k : ℝ) + 1 / 2) / n))) t) with hg_def
    have hg_sm : StronglyMeasurable g := by
      have h_sum : (fun t => ∑ k : Fin n,
          (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)).indicator
            (fun _ : ℝ => φ (quantile μ (((k : ℝ) + 1 / 2) / n))) t) =
          ∑ k : Fin n, (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)).indicator
            (fun _ : ℝ => φ (quantile μ (((k : ℝ) + 1 / 2) / n))) := by
        funext t; simp [Finset.sum_apply]
      rw [hg_def, h_sum]
      apply Finset.stronglyMeasurable_sum Finset.univ
      intro k _
      refine StronglyMeasurable.indicator ?_ measurableSet_Ico
      exact stronglyMeasurable_const
    have h_ae_eq : stepFun μ φ n =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      -- For t ∈ Ioo 0 1, t is in exactly one bin Ico (k/n) ((k+1)/n).
      obtain ⟨ht0, ht1⟩ := ht
      have ht_mem_Ico : t ∈ Ico (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
      rw [← iUnion_bins_eq_Ico n hn] at ht_mem_Ico
      simp only [Set.mem_iUnion] at ht_mem_Ico
      obtain ⟨k, hk⟩ := ht_mem_Ico
      rw [stepFun_eq_of_mem_Ico hn k hk]
      simp only [hg_def]
      rw [Finset.sum_eq_single k]
      · rw [Set.indicator_of_mem hk]
      · intro j _ hjk
        rw [Set.indicator_of_notMem]
        intro hj
        -- t ∈ bin k ∩ bin j is contradiction (they are disjoint).
        have hd := bins_pairwise_disjoint n hjk
        exact (Set.disjoint_iff.mp hd) ⟨hj, hk⟩
      · intro h; exact absurd (Finset.mem_univ _) h
    exact hg_sm.aestronglyMeasurable.congr h_ae_eq.symm
  · -- n = 0, stepFun is constant (binMidpoint 0 = 0, so stepFun 0 t = φ (quantile μ 0)).
    push Not at hn
    interval_cases n
    unfold stepFun binMidpoint
    simp only [Nat.cast_zero, zero_mul, Nat.floor_zero, div_zero]
    exact aestronglyMeasurable_const

/-- The integral of the step function over `Ioo 0 1` equals the midpoint Riemann sum. -/
-- `_hφ` unused: the integral is a finite sum over bins where `stepFun` is constant, computed
-- without appealing to continuity of `φ`; kept so the hypothesis matches the calling context.
lemma integral_stepFun_Ioo {φ : ℝ → ℝ} (_hφ : Continuous φ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in Ioo (0 : ℝ) 1, stepFun μ φ n t
      = (1 / n) * ∑ k : Fin n, φ (quantile μ (((k : ℝ) + 1 / 2) / n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Replace `Ioo 0 1` with `Ico 0 1` (they differ by a measure-zero point).
  have h_ioo_diff : Ioo (0 : ℝ) 1 \ Ico (0 : ℝ) 1 = ∅ := by
    ext x
    constructor
    · rintro ⟨⟨hx0, hx1⟩, h⟩
      exfalso; exact h ⟨hx0.le, hx1⟩
    · intro h; exact absurd h (by simp)
  have h_ico_diff : Ico (0 : ℝ) 1 \ Ioo (0 : ℝ) 1 ⊆ {0} := by
    intro x hx
    obtain ⟨⟨hx0, hx1⟩, h_not_ioo⟩ := hx
    -- hx0 : 0 ≤ x, hx1 : x < 1, h_not_ioo : ¬ (0 < x ∧ x < 1).
    -- Since x < 1, the ¬ clause forces ¬ 0 < x, i.e., x ≤ 0. Combined with 0 ≤ x: x = 0.
    have hx0' : x ≤ 0 := not_lt.mp fun h => h_not_ioo ⟨h, hx1⟩
    exact mem_singleton_iff.mpr (le_antisymm hx0' hx0)
  have h_ae_eq_set : Ioo (0 : ℝ) 1 =ᵐ[volume] Ico (0 : ℝ) 1 := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [h_ioo_diff]; exact measure_empty
    · exact measure_mono_null h_ico_diff (by rw [Real.volume_singleton])
  have h_ioo_eq : ∫ t in Ioo (0 : ℝ) 1, stepFun μ φ n t
      = ∫ t in Ico (0 : ℝ) 1, stepFun μ φ n t := setIntegral_congr_set h_ae_eq_set
  rw [h_ioo_eq]
  -- Split `Ico 0 1` into the disjoint union of bins and integrate each constant.
  rw [← iUnion_bins_eq_Ico n hn]
  rw [integral_iUnion_fintype (s := fun k : Fin n => Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))
      (μ := volume) (f := stepFun μ φ n)
      (fun _ => measurableSet_Ico) (bins_pairwise_disjoint n) ?_]
  · -- Goal: ∑ k, ∫ t in Ico (k/n) ((k+1)/n), stepFun μ φ n t = (1/n) * ∑ k, φ (...).
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- On this bin, stepFun is constant equal to `φ (quantile μ ((k + 1/2)/n))`.
    have h_const : ∀ t ∈ Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        stepFun μ φ n t = φ (quantile μ (((k : ℝ) + 1 / 2) / n)) := by
      intro t ht; exact stepFun_eq_of_mem_Ico hn k ht
    rw [setIntegral_congr_fun measurableSet_Ico h_const]
    rw [setIntegral_const]
    -- Goal: (volume (Ico (k/n) ((k+1)/n))).real • c = (1/n) * c.
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have h_width : (((k : ℝ) + 1) / n - (k : ℝ) / n) = 1 / n := by
      rw [div_sub_div_same]; congr 1; ring
    have h_vol : (volume (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))).toReal = 1 / n := by
      rw [Real.volume_Ico, h_width]
      rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / n)]
    change (volume (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))).toReal •
        φ (quantile μ (((k : ℝ) + 1 / 2) / n)) = (1 / n) * _
    rw [h_vol]
    rfl
  · intro k
    -- IntegrableOn stepFun on Ico (k/n) ((k+1)/n): it's a constant there.
    have h_const : Set.EqOn (fun _ : ℝ => φ (quantile μ (((k : ℝ) + 1 / 2) / n)))
        (stepFun μ φ n) (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) := by
      intro t ht; exact (stepFun_eq_of_mem_Ico hn k ht).symm
    have h_vol_lt : (volume (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))) ≠ ⊤ := by
      rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
    have h_const_intg : IntegrableOn
        (fun _ : ℝ => φ (quantile μ (((k : ℝ) + 1 / 2) / n)))
        (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) volume :=
      integrableOn_const h_vol_lt
    exact MeasureTheory.IntegrableOn.congr_fun h_const_intg h_const
      (measurableSet_Ico : MeasurableSet (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)))

/-! ### Pointwise convergence of the step function -/

/-- For `t ∈ Ioo 0 1` where `quantile μ` is continuous within `Ioo 0 1` at `t`, the step function
value `stepFun μ φ n t` converges to `φ (quantile μ t)` as `n → ∞`. -/
lemma tendsto_stepFun_of_continuousWithinAt {φ : ℝ → ℝ} (hφ : Continuous φ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (h_qcts : ContinuousWithinAt (quantile μ) (Ioo (0 : ℝ) 1) t) :
    Tendsto (fun n : ℕ => stepFun μ φ n t) atTop (𝓝 (φ (quantile μ t))) := by
  unfold stepFun
  obtain ⟨ht0, ht1⟩ := ht
  -- `binMidpoint n t → t`, eventually inside `Ioo 0 1`; compose with continuity of `quantile μ`
  -- within `Ioo 0 1` and of `φ`.
  have h_mid_tendsto : Tendsto (fun n : ℕ => binMidpoint n t) atTop (𝓝 t) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Choose N ≥ 1/ε + 1.
    obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / ε)
    set N := max N0 1 with hN_def
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℕ) ≤ N := le_max_right _ _
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp this) |>.bot_lt
    have hN_gt : 1 / ε < (N : ℝ) := by
      calc 1 / ε < (N0 : ℝ) := hN0
        _ ≤ (N : ℝ) := by exact_mod_cast le_max_left _ _
    refine ⟨N, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hNpos hnN
    have habs : |binMidpoint n t - t| ≤ 1 / n := abs_binMidpoint_sub_le hn1 ht0.le ht1
    rw [Real.dist_eq]
    have h_one_div : 1 / (n : ℝ) ≤ 1 / (N : ℝ) := one_div_le_one_div_of_le hNpos hnN
    have h_one_lt : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN_gt
    have h_one_div_lt : 1 / (N : ℝ) < ε := (div_lt_iff₀ hNpos).mpr (by linarith)
    linarith
  have h_mid_in : ∀ᶠ n in atTop, binMidpoint n t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact binMidpoint_mem_Ioo hn ht0.le ht1
  have h_quant_tendsto : Tendsto (fun n : ℕ => quantile μ (binMidpoint n t)) atTop
      (𝓝 (quantile μ t)) := by
    rw [ContinuousWithinAt] at h_qcts
    -- h_qcts : Tendsto (quantile μ) (𝓝[Ioo 0 1] t) (𝓝 (quantile μ t)).
    have h_mid_nhds_within : Tendsto (fun n : ℕ => binMidpoint n t) atTop
        (𝓝[Ioo (0 : ℝ) 1] t) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h_mid_tendsto, h_mid_in⟩
    exact h_qcts.comp h_mid_nhds_within
  -- Compose with `φ` continuous.
  exact (hφ.tendsto _).comp h_quant_tendsto

/-- On `Ioo 0 1`, the quantile function is continuous except on a countable set. -/
lemma countable_not_continuousWithinAt_quantile [IsProbabilityMeasure μ] :
    {t | t ∈ Ioo (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt (quantile μ) (Ioo (0 : ℝ) 1) t}.Countable :=
  (monotoneOn_quantile (μ := μ)).countable_not_continuousWithinAt

/-- Pointwise AE convergence of step functions on `Ioo 0 1`. -/
lemma stepFun_tendsto_ae [IsProbabilityMeasure μ] {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun n : ℕ => stepFun μ φ n t) atTop (𝓝 (φ (quantile μ t))) := by
  -- The set of discontinuity points of `quantile μ` on `Ioo 0 1` is countable, hence null
  -- under volume. At every other point of `Ioo 0 1`, the step functions converge.
  rw [ae_restrict_iff' measurableSet_Ioo]
  have h_small :
      {t | t ∈ Ioo (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt (quantile μ) (Ioo (0 : ℝ) 1) t}.Countable :=
    countable_not_continuousWithinAt_quantile
  have h_null : volume {t : ℝ |
      t ∈ Ioo (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt (quantile μ) (Ioo (0 : ℝ) 1) t} = 0 :=
    h_small.measure_zero _
  -- We reduce to showing: volume of `{t | ¬ (t ∈ Ioo → ConvergesAt t)}` is zero.
  rw [ae_iff]
  apply measure_mono_null _ h_null
  -- Goal: {t | ¬ (t ∈ Ioo → Tendsto ...)} ⊆ {t | t ∈ Ioo ∧ ¬ ContinuousWithinAt ...}.
  intro t ht
  simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
  obtain ⟨h_t_in, h_no_conv⟩ := ht
  refine ⟨h_t_in, ?_⟩
  intro h_cts
  exact h_no_conv (tendsto_stepFun_of_continuousWithinAt hφ h_t_in h_cts)

/-! ### Integrability of the step function -/

/-- The constant `M` is integrable on `Ioo 0 1` (a finite-measure set). -/
lemma integrable_const_Ioo (M : ℝ) :
    Integrable (fun _ : ℝ => M) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine integrable_const _

/-- The step function is integrable on `Ioo 0 1`. -/
lemma integrable_stepFun_Ioo {φ : ℝ → ℝ} (hφ : Continuous φ) {M : ℝ} (hM : ∀ x, |φ x| ≤ M)
    (n : ℕ) : Integrable (stepFun μ φ n) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine ⟨aestronglyMeasurable_stepFun hφ n, ?_⟩
  -- HasFiniteIntegral: bounded by M on finite-measure set.
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  refine MeasureTheory.HasFiniteIntegral.mono' (g := fun _ => M) ?_ ?_
  · -- `HasFiniteIntegral (const M)` on restrict to Ioo 0 1.
    exact (integrable_const_Ioo M).2
  · -- `‖stepFun μ φ n t‖ ≤ M` everywhere.
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [Real.norm_eq_abs]
    exact abs_stepFun_le hM n t

/-! ### Main theorem -/

/-- **Midpoint Riemann sum convergence for bounded continuous `φ`.** The midpoint Riemann sums of
`φ ∘ quantile μ` at resolution `n+1` converge to `∫ φ dμ`. -/
theorem tendsto_integral_of_quantile_midpoint [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hφ : Continuous φ) {M : ℝ} (hM : ∀ x, |φ x| ≤ M) :
    Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑ k : Fin (n + 1), φ (quantile μ (((k : ℝ) + 1/2) / (n + 1))))
      atTop (𝓝 (∫ x, φ x ∂μ)) := by
  -- Reduce to `∫ t in Ioo 0 1, φ ∘ quantile μ`.
  have h_rewrite_lhs : (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ k : Fin (n + 1), φ (quantile μ (((k : ℝ) + 1/2) / (n + 1))))
      = fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1, stepFun μ φ (n + 1) t := by
    funext n
    rw [integral_stepFun_Ioo hφ (Nat.le_add_left 1 n)]
    push_cast
    ring
  rw [h_rewrite_lhs]
  -- Reduce RHS.
  have h_rhs : ∫ x, φ x ∂μ = ∫ t in Ioo (0 : ℝ) 1, φ (quantile μ t) := by
    exact integral_eq_integral_quantile φ hφ.aestronglyMeasurable
  rw [h_rhs]
  -- Apply DCT: stepFun μ φ (n+1) → φ ∘ quantile μ ae, bounded by M, on Ioo 0 1.
  set F : ℕ → ℝ → ℝ := fun n => stepFun μ φ (n + 1) with hF_def
  change Tendsto (fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1, F n t) atTop
    (𝓝 (∫ t in Ioo (0 : ℝ) 1, φ (quantile μ t)))
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ => M) ?_ ?_ ?_ ?_
  · -- AE strongly measurable.
    intro n
    exact aestronglyMeasurable_stepFun hφ (n + 1)
  · -- Bound integrable.
    exact integrable_const_Ioo M
  · -- Pointwise bound.
    intro n
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Real.norm_eq_abs]
      exact abs_stepFun_le hM (n + 1) t)
  · -- Pointwise AE convergence: stepFun μ φ (n+1) t → φ (quantile μ t).
    have h_ae := stepFun_tendsto_ae (μ := μ) hφ
    -- Shift index from `n` to `n + 1`.
    filter_upwards [h_ae] with t ht
    exact ht.comp (Filter.tendsto_add_atTop_nat 1)

end MeasureTheory.Measure

end
