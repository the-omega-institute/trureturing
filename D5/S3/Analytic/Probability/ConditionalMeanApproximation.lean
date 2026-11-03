/- GID: D5/S3/Analytic/Probability/ConditionalMeanApproximation
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/ConditionalMeanApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: ConditionalMeanApproximation for compact scalar martingale transport. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import D5.S3.Analytic.Probability.ConditionalMeanAtoms
import Mathlib.MeasureTheory.Function.Floor


open MeasureTheory Set Filter Topology

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace Econlib.Probability
namespace DiscreteLaw

/-- Bin index function: `binIndex n t = ⌊n·t⌋₊`. For `t ∈ Ioo 0 1` and `n ≥ 1`, this sits in
`[0, n-1]`, so it represents a bin in `Fin n`. -/
private def binIndex (n : ℕ) (t : ℝ) : ℕ := ⌊(n : ℝ) * t⌋₊

/-- For `t ∈ Ioo 0 1` and `n ≥ 1`, the bin index is in `Fin n`. -/
private lemma binIndex_lt {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    binIndex n t < n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_nt_nn : 0 ≤ (n : ℝ) * t := mul_nonneg hnpos.le ht.1.le
  have h_nt_lt : (n : ℝ) * t < n := by nlinarith [ht.2]
  rw [binIndex, Nat.floor_lt h_nt_nn]
  exact h_nt_lt

/-- For `t ∈ Ioc (k/n) ((k+1)/n)` with `k : Fin n` and `n ≥ 1`, `binIndex n t = k` (unless
`t = (k+1)/n` is a right endpoint of a bin, which is a measure-zero edge case handled via `Ico`
conversion). On `Ico (k/n) ((k+1)/n)`, `binIndex n t = k`. -/
private lemma binIndex_eq_of_mem_Ico {n : ℕ} (hn : 1 ≤ n) (k : Fin n) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    binIndex n t = (k : ℕ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨ht_le, ht_lt⟩ := ht
  have h_nt_ge : (k : ℝ) ≤ n * t := by
    have := (div_le_iff₀ hnpos).mp ht_le
    linarith
  have h_nt_lt : n * t < (k : ℝ) + 1 := by
    have := (lt_div_iff₀ hnpos).mp ht_lt
    linarith
  have h_nt_nn : 0 ≤ (n : ℝ) * t := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  unfold binIndex
  rw [Nat.floor_eq_iff h_nt_nn]
  refine ⟨h_nt_ge, ?_⟩
  linarith

/-- The conditional-mean step function: For `t ∈ Ioo 0 1`, it returns
`φ(condMeanAtom μ n _ (binIndex n t))` when `binIndex n t < n`, and a default `φ(atom_0)`
otherwise. This is the step-function analog of `stepFun` in the quantile midpoint construction. -/
private noncomputable def condStepFun (μ : ProbDist ℝ) (φ : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (t : ℝ) : ℝ :=
  if h : binIndex n t < n then
    φ (DiscreteLaw.condMeanAtom μ n hn ⟨binIndex n t, h⟩)
  else
    φ (DiscreteLaw.condMeanAtom μ n hn ⟨0, hn⟩)

/-- On `Ico (k/n) ((k+1)/n)` with `k : Fin n`, the step function is constant. -/
private lemma condStepFun_eq_of_mem_Ico {μ : ProbDist ℝ} {φ : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (k : Fin n) {t : ℝ} (ht : t ∈ Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    condStepFun μ φ n hn t = φ (DiscreteLaw.condMeanAtom μ n hn k) := by
  unfold condStepFun
  have h_idx : binIndex n t = (k : ℕ) := binIndex_eq_of_mem_Ico hn k ht
  have h_idx_lt : binIndex n t < n := by rw [h_idx]; exact k.isLt
  rw [dif_pos h_idx_lt]
  congr 1
  apply congrArg
  exact Fin.ext h_idx

/-- The step function is bounded by `M` whenever `|φ| ≤ M`. -/
private lemma abs_condStepFun_le {μ : ProbDist ℝ} {φ : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |φ x| ≤ M)
    {n : ℕ} (hn : 0 < n) (t : ℝ) : |condStepFun μ φ n hn t| ≤ M := by
  unfold condStepFun
  split
  · exact hM _
  · exact hM _

/-- AE strong measurability of `condStepFun` on `Ioo 0 1`. -/
private lemma aestronglyMeasurable_condStepFun {μ : ProbDist ℝ} {φ : ℝ → ℝ}
    (_hφ : Continuous φ) {n : ℕ} (hn : 0 < n) :
    AEStronglyMeasurable (condStepFun μ φ n hn)
      ((MeasureTheory.volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
  -- On each bin `Ico (k/n) ((k+1)/n)`, the step function is constant.
  -- The union of these bins equals `Ico 0 1`, which agrees with `Ioo 0 1` a.e.
  set g : ℝ → ℝ := (fun t => ∑ k : Fin n,
    (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)).indicator
      (fun _ : ℝ => φ (DiscreteLaw.condMeanAtom μ n hn k)) t) with hg_def
  have hg_sm : StronglyMeasurable g := by
    rw [hg_def, ← Finset.sum_fn]
    apply Finset.stronglyMeasurable_sum Finset.univ
    intro k _
    exact (stronglyMeasurable_const (b := φ (DiscreteLaw.condMeanAtom μ n hn k))).indicator
      measurableSet_Ico
  have h_ae_eq : condStepFun μ φ n hn =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] g := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    obtain ⟨ht0, ht1⟩ := ht
    have ht_mem_Ico : t ∈ Ico (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
    rw [← MeasureTheory.Measure.iUnion_bins_eq_Ico n hn] at ht_mem_Ico
    simp only [Set.mem_iUnion] at ht_mem_Ico
    obtain ⟨k, hk⟩ := ht_mem_Ico
    rw [condStepFun_eq_of_mem_Ico hn k hk]
    simp only [hg_def]
    rw [Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem hk]
    · intro j _ hjk
      rw [Set.indicator_of_notMem]
      intro hj
      have hd := MeasureTheory.Measure.bins_pairwise_disjoint n hjk
      exact (Set.disjoint_iff.mp hd) ⟨hj, hk⟩
    · intro h; exact absurd (Finset.mem_univ _) h
  exact hg_sm.aestronglyMeasurable.congr h_ae_eq.symm

/-- The integral of `condStepFun` on `Ioo 0 1` equals the conditional-mean average. -/
private lemma integral_condStepFun_Ioo {μ : ProbDist ℝ} {φ : ℝ → ℝ} (_hφ : Continuous φ)
    {n : ℕ} (hn : 0 < n) :
    ∫ t in Ioo (0 : ℝ) 1, condStepFun μ φ n hn t
      = (1 / n) * ∑ k : Fin n, φ (DiscreteLaw.condMeanAtom μ n hn k) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Replace `Ioo 0 1` with `Ico 0 1` (they differ by a measure-zero point).
  have h_ae_eq_set : Ioo (0 : ℝ) 1 =ᵐ[volume] Ico (0 : ℝ) 1 :=
    MeasureTheory.Ioo_ae_eq_Ico
  have h_ioo_eq : ∫ t in Ioo (0 : ℝ) 1, condStepFun μ φ n hn t
      = ∫ t in Ico (0 : ℝ) 1, condStepFun μ φ n hn t := setIntegral_congr_set h_ae_eq_set
  rw [h_ioo_eq]
  -- Split `Ico 0 1` into the disjoint union of bins.
  rw [← MeasureTheory.Measure.iUnion_bins_eq_Ico n hn]
  rw [MeasureTheory.integral_iUnion_fintype
      (s := fun k : Fin n => Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))
      (μ := volume) (f := condStepFun μ φ n hn)
      (fun _ => measurableSet_Ico) (MeasureTheory.Measure.bins_pairwise_disjoint n) ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h_const : ∀ t ∈ Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        condStepFun μ φ n hn t = φ (DiscreteLaw.condMeanAtom μ n hn k) := by
      intro t ht; exact condStepFun_eq_of_mem_Ico hn k ht
    rw [setIntegral_congr_fun measurableSet_Ico h_const]
    rw [setIntegral_const]
    have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have h_width : (((k : ℝ) + 1) / n - (k : ℝ) / n) = 1 / n := by
      rw [show ((k : ℝ) + 1) / n - (k : ℝ) / n = ((k : ℝ) + 1 - k) / n from
        (sub_div _ _ _).symm]
      congr 1; ring
    have h_vol : (volume (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))).toReal = 1 / n := by
      rw [Real.volume_Ico, h_width]
      rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / n)]
    change (volume (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))).toReal •
        φ (DiscreteLaw.condMeanAtom μ n hn k) = (1 / n) * _
    rw [h_vol]
    rfl
  · intro k
    have h_const : Set.EqOn (fun _ : ℝ => φ (DiscreteLaw.condMeanAtom μ n hn k))
        (condStepFun μ φ n hn) (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) := by
      intro t ht; exact (condStepFun_eq_of_mem_Ico hn k ht).symm
    have h_vol_lt : (volume (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n))) ≠ ⊤ := by
      rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
    have h_const_intg : IntegrableOn
        (fun _ : ℝ => φ (DiscreteLaw.condMeanAtom μ n hn k))
        (Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) volume :=
      integrableOn_const h_vol_lt
    exact MeasureTheory.IntegrableOn.congr_fun h_const_intg h_const measurableSet_Ico

/-- Integrating `φ` against the atomization measure equals the conditional-mean step-function
integral over `Ioo 0 1`. -/
private lemma integral_toProbDist_condMeanAtomize {μ : ProbDist ℝ} {φ : ℝ → ℝ}
    (hφ : Continuous φ) {n : ℕ} (hn : 0 < n) :
    ∫ x, φ x ∂(DiscreteLaw.condMeanAtomize μ n hn).toProbDist.toMeasure
      = (1 / n) * ∑ k : Fin n, φ (DiscreteLaw.condMeanAtom μ n hn k) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Expand the measure as a sum of Diracs with uniform weights 1/n.
  rw [DiscreteLaw.toProbDist_toMeasure]
  rw [integral_finset_sum_measure (fun i _ => by
    have h_norm : ‖φ ((DiscreteLaw.condMeanAtomize μ n hn).atom i)‖ₑ < ⊤ := by
      exact ENNReal.coe_lt_top
    refine (MeasureTheory.integrable_dirac' (a :=
      (DiscreteLaw.condMeanAtomize μ n hn).atom i) hφ.stronglyMeasurable
      h_norm).smul_measure ENNReal.ofReal_ne_top)]
  -- Simplify each summand.
  have h_sum : ∀ i : Fin n,
      ∫ x, φ x ∂(ENNReal.ofReal ((DiscreteLaw.condMeanAtomize μ n hn).weight i) •
          Measure.dirac ((DiscreteLaw.condMeanAtomize μ n hn).atom i))
      = (1 / n) * φ (DiscreteLaw.condMeanAtom μ n hn i) := by
    intro i
    rw [integral_smul_measure, integral_dirac' _ _ hφ.stronglyMeasurable, smul_eq_mul]
    change ENNReal.toReal (ENNReal.ofReal ((1 : ℝ) / n)) *
        φ (DiscreteLaw.condMeanAtom μ n hn i) = (1 / n) * _
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / n)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact h_sum i

/-- For `t ∈ Ioo 0 1` and `n ≥ 1`, the bin containing `t` (namely `Ico (k/n) ((k+1)/n)` where
`k = binIndex n t`) has endpoints within `1/n` of `t`, both endpoints in `[0, 1]`. -/
private lemma bin_of_binIndex_bounds {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (binIndex n t : ℝ) / n ≤ t ∧ t < ((binIndex n t : ℝ) + 1) / n ∧
    ((binIndex n t : ℝ) + 1) / n - (binIndex n t : ℝ) / n = 1 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_nt_nn : 0 ≤ (n : ℝ) * t := mul_nonneg hnpos.le ht.1.le
  have hfl_le : ((binIndex n t : ℕ) : ℝ) ≤ (n : ℝ) * t := by
    unfold binIndex; exact Nat.floor_le h_nt_nn
  have hlt_fl : (n : ℝ) * t < ((binIndex n t : ℕ) : ℝ) + 1 := by
    unfold binIndex; exact Nat.lt_floor_add_one ((n : ℝ) * t)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hnpos]; linarith
  · rw [lt_div_iff₀ hnpos]; linarith
  · rw [show (((binIndex n t : ℝ)) + 1) / n - (binIndex n t : ℝ) / n
        = ((binIndex n t : ℝ) + 1 - binIndex n t) / n from (sub_div _ _ _).symm]
    congr 1; ring

/-- At a continuity point `t ∈ Ioo 0 1` of `quantile μ` (within `Ioo 0 1`),
`condMeanAtom μ n hn (binIndex n t)` converges to `quantile μ t` as `n → ∞`: The bin containing `t`
shrinks to `{t}`, so its quantile average converges to `quantile μ t` by continuity. -/
private lemma tendsto_condMeanAtom_of_continuousWithinAt
    {a b : ℝ} {μ : ProbDist ℝ} (h : μ.supportsOn (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (h_qcts : ContinuousWithinAt (MeasureTheory.Measure.quantile μ.toMeasure)
      (Ioo (0 : ℝ) 1) t) :
    Tendsto (fun n : ℕ => if h : binIndex (n + 1) t < (n + 1) then
        DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨binIndex (n + 1) t, h⟩
      else DiscreteLaw.condMeanAtom μ (n + 1) (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩)
      atTop (𝓝 (MeasureTheory.Measure.quantile μ.toMeasure t)) := by
  -- Eventually binIndex (n+1) t < n+1, so the conditional branch taken is the first.
  have h_idx_lt : ∀ᶠ n in atTop, binIndex (n + 1) t < n + 1 := by
    filter_upwards with n
    exact binIndex_lt (Nat.succ_le_succ (Nat.zero_le n)) ht
  -- Reduce to showing `condMeanAtom μ (n+1) _ ⟨binIndex (n+1) t, _⟩ → quantile μ t`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- Use continuity of `quantile` within `Ioo 0 1` at `t`.
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at h_qcts
  obtain ⟨δ, hδ_pos, hδ⟩ := h_qcts (ε / 2) hε2
  -- Eventually 1/(n+1) < δ and bin is inside Ioo 0 1.
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  -- Choose N large enough that 1/(N+1) < δ and bin fits in Ioo 0 1.
  -- The bin containing `t` has width 1/(n+1) and contains `t`, so its endpoints are within
  -- 1/(n+1) of t. Need 1/(n+1) < δ AND the left endpoint > 0 AND the right endpoint < 1.
  obtain ⟨N1, hN1⟩ := exists_nat_gt (1 / t)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (1 / (1 - t))
  have ht_pos : 0 < t := ht.1
  have ht_sub_pos : 0 < 1 - t := by linarith [ht.2]
  set N := max (max (max N0 N1) N2) 1 with hN_def
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn_succ_ge_1 : (1 : ℕ) ≤ n + 1 := Nat.le_add_left 1 n
  -- 1/(n+1) < δ.
  have h_np1_R_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hN0_le_n : (N0 : ℝ) ≤ (n : ℝ) := by
    have : N0 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _) |>.trans (le_max_left _ _)
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact_mod_cast le_trans this hn
  have h_small_inv : 1 / ((n + 1 : ℕ) : ℝ) < δ := by
    have h1 : 1 / δ < (n + 1 : ℕ) := by
      calc 1 / δ < (N0 : ℝ) := hN0
        _ ≤ (n : ℝ) := hN0_le_n
        _ < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [div_lt_iff₀ h_np1_R_pos, mul_comm]
    rw [div_lt_iff₀ hδ_pos] at h1
    linarith
  -- Analogous: bin's left endpoint > 0.
  have hN1_le_n : (N1 : ℝ) ≤ (n : ℝ) := by
    have hN1_le : N1 ≤ N := by
      calc N1 ≤ max N0 N1 := le_max_right _ _
        _ ≤ max (max N0 N1) N2 := le_max_left _ _
        _ ≤ max (max (max N0 N1) N2) 1 := le_max_left _ _
    exact_mod_cast le_trans hN1_le hn
  have hN2_le_n : (N2 : ℝ) ≤ (n : ℝ) := by
    have hN2_le : N2 ≤ N := by
      calc N2 ≤ max (max N0 N1) N2 := le_max_right _ _
        _ ≤ max (max (max N0 N1) N2) 1 := le_max_left _ _
    exact_mod_cast le_trans hN2_le hn
  -- Bin endpoints.
  obtain ⟨hL_le, hR_lt, _⟩ := bin_of_binIndex_bounds hn_succ_ge_1 ht
  set k_nat : ℕ := binIndex (n + 1) t with hk_def
  have hk_lt : k_nat < n + 1 := binIndex_lt hn_succ_ge_1 ht
  -- `k_nat/(n+1) ≤ t < (k_nat+1)/(n+1)`, width `1/(n+1)`. We bound `|condMeanAtom - q_μ(t)|` by the
  -- bin-average of `|q_μ(u) - q_μ(t)|`, using `u ∈ Ioo 0 1` a.e. on the bin and continuity of
  -- `q_μ`.
  have hN1_gt : (1 : ℝ) / t < (N1 : ℝ) := hN1
  have hN2_gt : (1 : ℝ) / (1 - t) < (N2 : ℝ) := hN2
  have h_one_div_np1_lt_t : 1 / ((n + 1 : ℕ) : ℝ) < t := by
    have : 1 / t < (n : ℝ) := lt_of_lt_of_le hN1_gt hN1_le_n
    have h_np1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : 1 / t < ((n + 1 : ℕ) : ℝ) := lt_trans this h_np1
    rw [div_lt_iff₀ ht_pos] at this
    rw [div_lt_iff₀ h_np1_R_pos, mul_comm]
    linarith
  have h_one_div_np1_lt_sub : 1 / ((n + 1 : ℕ) : ℝ) < 1 - t := by
    have : 1 / (1 - t) < (n : ℝ) := lt_of_lt_of_le hN2_gt hN2_le_n
    have h_np1 : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : 1 / (1 - t) < ((n + 1 : ℕ) : ℝ) := lt_trans this h_np1
    rw [div_lt_iff₀ ht_sub_pos] at this
    rw [div_lt_iff₀ h_np1_R_pos, mul_comm]
    linarith
  -- Now: t - 1/(n+1) > 0 and t + 1/(n+1) < 1.
  -- Bounds on bin endpoints.
  -- Left endpoint: k_nat/(n+1) ≥ t - 1/(n+1) (since t < (k_nat+1)/(n+1) implies
  -- (n+1) t < k_nat + 1 implies k_nat > (n+1)t - 1 implies k_nat / (n+1) > t - 1/(n+1)).
  have h_left_ge : t - 1 / ((n + 1 : ℕ) : ℝ) ≤ (k_nat : ℝ) / (n + 1 : ℕ) := by
    have h_np1_t : ((n + 1 : ℕ) : ℝ) * t < (k_nat : ℝ) + 1 := by
      rw [lt_div_iff₀ h_np1_R_pos] at hR_lt; linarith
    have h_t_lt : t < ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) := by
      rw [lt_div_iff₀ h_np1_R_pos]; linarith
    have : ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) =
        (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [add_div]
    linarith
  -- Right endpoint: (k_nat+1)/(n+1) ≤ t + 1/(n+1).
  have h_right_le : ((k_nat : ℝ) + 1) / (n + 1 : ℕ) ≤ t + 1 / ((n + 1 : ℕ) : ℝ) := by
    have hk_le_nt : (k_nat : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * t := by
      rw [div_le_iff₀ h_np1_R_pos] at hL_le; linarith
    have : ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) =
        (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by rw [add_div]
    rw [this]
    have hk_le_t : (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ t := hL_le
    linarith
  -- So bin ⊆ Ioo 0 1 (using h_left_ge: left endpoint ≥ t - 1/(n+1) > 0; h_right_le: right
  -- endpoint ≤ t + 1/(n+1) < 1).
  have h_L_pos : 0 < (k_nat : ℝ) / (n + 1 : ℕ) := by
    have : t - 1 / ((n + 1 : ℕ) : ℝ) > 0 := by linarith
    linarith
  have h_R_lt_1 : ((k_nat : ℝ) + 1) / (n + 1 : ℕ) < 1 := by
    have : t + 1 / ((n + 1 : ℕ) : ℝ) < 1 := by linarith
    linarith
  -- Now evaluate the dif.
  rw [dif_pos hk_lt]
  -- Goal: dist (condMeanAtom μ (n+1) _ ⟨k_nat, hk_lt⟩) (quantile μ t) < ε.
  -- Unfold condMeanAtom: (n+1) · ∫_{Ioc (k_nat/(n+1)) ((k_nat+1)/(n+1))} quantile μ u du.
  unfold DiscreteLaw.condMeanAtom
  -- Express quantile μ t = (n+1) · ∫_{bin} quantile μ t du (constant * volume 1/(n+1)).
  set bin : Set ℝ := Set.Ioc ((k_nat : ℝ) / (n + 1 : ℕ))
    (((k_nat : ℝ) + 1) / (n + 1 : ℕ)) with hbin_def
  have h_bin_subset_Ioo : bin ⊆ Ioo (0 : ℝ) 1 := by
    rw [hbin_def]
    intro u hu
    refine ⟨lt_of_lt_of_le h_L_pos hu.1.le, lt_of_le_of_lt hu.2 h_R_lt_1⟩
  -- Volume of bin is 1/(n+1).
  have h_width_eq : (((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) - (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ))
      = 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [show ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) - (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) =
      ((k_nat : ℝ) + 1 - k_nat) / ((n + 1 : ℕ) : ℝ) from (sub_div _ _ _).symm]
    congr 1; ring
  have hbin_vol_real : (MeasureTheory.volume : Measure ℝ).real bin = 1 / (n + 1 : ℕ) := by
    rw [hbin_def, Real.volume_real_Ioc_of_le]
    · exact h_width_eq
    · have : (k_nat : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ ((k_nat : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ h_np1_R_pos.le; linarith
      exact this
  have hbin_vol : (MeasureTheory.volume : Measure ℝ) bin ≠ ⊤ := by
    rw [hbin_def, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hbin_meas : MeasurableSet bin := by
    rw [hbin_def]; exact measurableSet_Ioc
  -- Integrability of quantile on bin (using bounded support).
  have h_int_quantile : IntegrableOn (MeasureTheory.Measure.quantile μ.toMeasure)
      bin := by
    rw [hbin_def]
    exact integrableOn_quantile_bin h (Nat.succ_pos n) ⟨k_nat, hk_lt⟩
  have h_int_const : IntegrableOn (fun _ : ℝ => MeasureTheory.Measure.quantile μ.toMeasure t)
      bin volume := integrableOn_const hbin_vol
  -- Integrand bound on bin: for u ∈ bin, |quantile μ u - quantile μ t| < ε.
  -- First, u ∈ Ioo 0 1 (above). Second, |u - t| ≤ 1/(n+1) < δ.
  have h_bin_ae_bound : ∀ᵐ u ∂(MeasureTheory.volume.restrict bin),
      |MeasureTheory.Measure.quantile μ.toMeasure u
        - MeasureTheory.Measure.quantile μ.toMeasure t| < ε / 2 := by
    rw [MeasureTheory.ae_restrict_iff' hbin_meas]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hu_Ioo : u ∈ Ioo (0 : ℝ) 1 := h_bin_subset_Ioo hu
    -- |u - t| < δ.
    rw [hbin_def] at hu
    have hu_dist : dist u t < δ := by
      rw [Real.dist_eq]
      rcases le_or_gt u t with hle | hgt
      · -- u ≤ t: |u - t| = t - u. u > k_nat/(n+1) ≥ t - 1/(n+1), so t - u < 1/(n+1) < δ.
        rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        have : u > t - 1 / ((n + 1 : ℕ) : ℝ) := lt_of_le_of_lt h_left_ge hu.1
        linarith
      · -- u > t: |u - t| = u - t. u ≤ (k_nat+1)/(n+1) ≤ t + 1/(n+1), so u - t ≤ 1/(n+1) < δ.
        rw [abs_of_pos (sub_pos.mpr hgt)]
        have : u ≤ t + 1 / ((n + 1 : ℕ) : ℝ) := le_trans hu.2 h_right_le
        linarith
    have h_diff : dist (MeasureTheory.Measure.quantile μ.toMeasure u)
        (MeasureTheory.Measure.quantile μ.toMeasure t) < ε / 2 :=
      hδ hu_Ioo hu_dist
    rw [Real.dist_eq] at h_diff
    exact h_diff
  -- Integrate pointwise bound.
  -- We write:
  --   condMeanAtom - q(t) = (n+1) * ∫_{bin} q(u) - q(t) du = (n+1) * (∫_{bin} q u du - q(t)/(n+1))
  -- and |above| ≤ (n+1) * ∫_{bin} |q(u) - q(t)| du ≤ (n+1) * ε * (1/(n+1)) = ε.
  -- In practice, use ∫_{bin} q(u) - q(t) du = ∫_{bin} q(u) du - q(t) * vol(bin).
  have h_diff_int :
      (∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u)
      - (MeasureTheory.Measure.quantile μ.toMeasure t) * (1 / ((n + 1 : ℕ) : ℝ))
      = ∫ u in bin, (MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t) := by
    rw [integral_sub h_int_quantile h_int_const]
    rw [MeasureTheory.setIntegral_const]
    rw [hbin_vol_real, smul_eq_mul]
    ring
  -- Bound ∫|diff| ≤ ε * vol(bin).
  have h_int_diff_abs :
      ‖∫ u in bin, (MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t)‖
        ≤ (ε / 2) * (1 / ((n + 1 : ℕ) : ℝ)) := by
    have h_bound : ∀ᵐ u ∂(MeasureTheory.volume.restrict bin),
        ‖MeasureTheory.Measure.quantile μ.toMeasure u
            - MeasureTheory.Measure.quantile μ.toMeasure t‖ ≤ ε / 2 := by
      filter_upwards [h_bin_ae_bound] with u hu
      rw [Real.norm_eq_abs]
      linarith
    have h_fin : (MeasureTheory.volume : Measure ℝ) bin < ⊤ := by
      rw [hbin_def, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have := MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae (C := ε / 2) (s := bin)
      (f := fun u => MeasureTheory.Measure.quantile μ.toMeasure u
        - MeasureTheory.Measure.quantile μ.toMeasure t) h_fin h_bound
    rw [hbin_vol_real] at this
    linarith [this]
  -- Combine.
  rw [Real.dist_eq]
  -- Rewrite LHS as (n+1) * (∫ q(u) - q(t)/(n+1)) = (n+1) * ∫ (q(u) - q(t)).
  have h_cancel : ((n + 1 : ℕ) : ℝ) *
      ((MeasureTheory.Measure.quantile μ.toMeasure t) * (1 / ((n + 1 : ℕ) : ℝ))) =
      MeasureTheory.Measure.quantile μ.toMeasure t := by
    field_simp
  have h_lhs_eq :
      ((n + 1 : ℕ) : ℝ) * (∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u)
      - MeasureTheory.Measure.quantile μ.toMeasure t =
      ((n + 1 : ℕ) : ℝ) *
        ∫ u in bin, (MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t) := by
    rw [← h_diff_int, mul_sub]
    rw [show ((n + 1 : ℕ) : ℝ) *
        (MeasureTheory.Measure.quantile μ.toMeasure t * (1 / ((n + 1 : ℕ) : ℝ))) =
        MeasureTheory.Measure.quantile μ.toMeasure t from h_cancel]
  rw [h_lhs_eq]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
  have h_step : ((n + 1 : ℕ) : ℝ) * |∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u
          - MeasureTheory.Measure.quantile μ.toMeasure t|
      ≤ ε / 2 := by
    calc ((n + 1 : ℕ) : ℝ) * |∫ u in bin, MeasureTheory.Measure.quantile μ.toMeasure u
            - MeasureTheory.Measure.quantile μ.toMeasure t|
        ≤ ((n + 1 : ℕ) : ℝ) * ((ε / 2) * (1 / ((n + 1 : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := h_int_diff_abs
          rw [Real.norm_eq_abs] at this
          exact this
      _ = ε / 2 := by field_simp
  linarith

/-- At a continuity point `t ∈ Ioo 0 1` of `quantile μ` (within `Ioo 0 1`),
`condStepFun μ φ (n+1) _ t → φ(quantile μ t)`. -/
private lemma tendsto_condStepFun_of_continuousWithinAt
    {a b : ℝ} {μ : ProbDist ℝ} (h : μ.supportsOn (Icc a b))
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (h_qcts : ContinuousWithinAt (MeasureTheory.Measure.quantile μ.toMeasure)
      (Ioo (0 : ℝ) 1) t) :
    Tendsto (fun n : ℕ => condStepFun μ φ (n + 1) (Nat.succ_pos n) t) atTop
      (𝓝 (φ (MeasureTheory.Measure.quantile μ.toMeasure t))) := by
  -- Reduce to: the atom value tends to quantile μ t, then apply hφ.
  have h_atom := tendsto_condMeanAtom_of_continuousWithinAt h ht h_qcts
  have h_cts := (hφ.tendsto _).comp h_atom
  -- condStepFun is the if-dif around the atom; h_atom already matches this shape.
  convert h_cts using 1
  funext n
  unfold condStepFun
  simp only [Function.comp_apply]
  split_ifs with h1 <;> rfl

/-- AE pointwise convergence of `condStepFun (n+1)` on `Ioo 0 1`. -/
private lemma condStepFun_tendsto_ae
    {a b : ℝ} {μ : ProbDist ℝ} (h : μ.supportsOn (Icc a b))
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∀ᵐ t ∂((MeasureTheory.volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun n : ℕ => condStepFun μ φ (n + 1) (Nat.succ_pos n) t) atTop
        (𝓝 (φ (MeasureTheory.Measure.quantile μ.toMeasure t))) := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  have h_small :
      {t | t ∈ Ioo (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt
          (MeasureTheory.Measure.quantile μ.toMeasure) (Ioo (0 : ℝ) 1) t}.Countable :=
    MeasureTheory.Measure.countable_not_continuousWithinAt_quantile
      (μ := μ.toMeasure)
  have h_null : (MeasureTheory.volume : Measure ℝ) {t : ℝ |
      t ∈ Ioo (0 : ℝ) 1 ∧ ¬ ContinuousWithinAt
        (MeasureTheory.Measure.quantile μ.toMeasure) (Ioo (0 : ℝ) 1) t} = 0 :=
    h_small.measure_zero _
  rw [ae_iff]
  apply measure_mono_null _ h_null
  intro t ht
  simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
  obtain ⟨h_t_in, h_no_conv⟩ := ht
  refine ⟨h_t_in, ?_⟩
  intro h_cts
  exact h_no_conv (tendsto_condStepFun_of_continuousWithinAt h hφ h_t_in h_cts)

/-- **Weak convergence of conditional-mean atomization.** The `condMeanAtomize` of a
compactly-supported probability law converges weakly to the law itself. -/
theorem condMeanAtomize_tendsto {a b : ℝ} {μ : ProbDist ℝ} (h : μ.supportsOn (Icc a b)) :
    Filter.Tendsto (fun n : ℕ =>
      ((DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
        : MeasureTheory.ProbabilityMeasure ℝ))
      Filter.atTop (nhds μ) := by
  -- Use weak convergence characterization: it suffices to test against BC functions.
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φBC
  set φ : ℝ → ℝ := fun x => φBC x with hφ_def
  have hφ_cts : Continuous φ := φBC.continuous
  set M : ℝ := ‖φBC‖ with hM_def
  have hM : ∀ x, |φ x| ≤ M := fun x => by
    rw [hM_def]
    have := φBC.norm_coe_le_norm x
    simpa [Real.norm_eq_abs] using this
  -- The LHS equals `(1/(n+1)) * ∑_k φ(condMeanAtom μ (n+1) _ k) = ∫_{Ioo 0 1} condStepFun`.
  have h_lhs_eq : (fun n : ℕ => ∫ x, φBC x
      ∂((DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure))
      = fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1, condStepFun μ φ (n + 1) (Nat.succ_pos n) t := by
    funext n
    rw [integral_condStepFun_Ioo hφ_cts (Nat.succ_pos n)]
    rw [integral_toProbDist_condMeanAtomize hφ_cts (Nat.succ_pos n)]
  rw [h_lhs_eq]
  -- The RHS equals `∫_{Ioo 0 1} φ ∘ quantile μ`.
  have h_rhs : ∫ x, φBC x ∂μ.toMeasure
      = ∫ t in Ioo (0 : ℝ) 1, φ (MeasureTheory.Measure.quantile μ.toMeasure t) :=
    MeasureTheory.Measure.integral_eq_integral_quantile φ hφ_cts.aestronglyMeasurable
  change Filter.Tendsto _ Filter.atTop (nhds (∫ x, φBC x ∂μ.toMeasure))
  rw [h_rhs]
  -- Conclude by dominated convergence.
  set F : ℕ → ℝ → ℝ := fun n => condStepFun μ φ (n + 1) (Nat.succ_pos n) with hF_def
  change Filter.Tendsto (fun n : ℕ => ∫ t in Ioo (0 : ℝ) 1, F n t) Filter.atTop
    (nhds (∫ t in Ioo (0 : ℝ) 1, φ (MeasureTheory.Measure.quantile μ.toMeasure t)))
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ => M) ?_ ?_ ?_ ?_
  · intro n
    exact aestronglyMeasurable_condStepFun hφ_cts (Nat.succ_pos n)
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Real.norm_eq_abs]
      exact abs_condStepFun_le hM (Nat.succ_pos n) t)
  · exact condStepFun_tendsto_ae h hφ_cts

/-- **Convex order preservation under conditional-mean atomization.** If `μ ≼cx[a,b] ν`, the
conditional-mean atomizations at any resolution satisfy the discrete convex order. -/
theorem condMeanAtomize_convexOrder {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) (n : ℕ) (hn : 0 < n) :
    DiscreteLaw.ConvexOrder
      (DiscreteLaw.condMeanAtomize μ n hn)
      (DiscreteLaw.condMeanAtomize ν n hn) := by
  intro φ hφ
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
  -- Reduce weighted sum to unweighted sum by factoring out the uniform weight 1/n.
  simp only [condMeanAtomize, uniform]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- Use monotonicity of scaling by 1/n ≥ 0.
  have hn_inv_nonneg : (0 : ℝ) ≤ 1 / n := by positivity
  apply mul_le_mul_of_nonneg_left _ hn_inv_nonneg
  -- Reduce `∑ φ(condMeanAtom μ) ≤ ∑ φ(condMeanAtom ν)` to `sum_convex_le_of_partial_sum_ge`, whose
  -- hypotheses are monotone atoms, equal total sums, and a partial-sum comparison.
  set x : Fin n → ℝ := fun k => condMeanAtom μ n hn k with hx_def
  set y : Fin n → ℝ := fun k => condMeanAtom ν n hn k with hy_def
  -- Monotonicity of x and y.
  have hx_mono : Monotone x := condMeanAtom_monotone h.support_left hn
  have hy_mono : Monotone y := condMeanAtom_monotone h.support_right hn
  -- Integrability of id under μ and ν.
  have hμ_int : Integrable (fun t : ℝ => t) μ.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_left
  have hν_int : Integrable (fun t : ℝ => t) ν.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_right
  -- Equal total sums: ∑ x = n · μ.expect id = n · ν.expect id = ∑ y.
  have hμ_mean : (condMeanAtomize μ n hn).mean = μ.expect id :=
    condMeanAtomize_mean_eq hμ_int n hn
  have hν_mean : (condMeanAtomize ν n hn).mean = ν.expect id :=
    condMeanAtomize_mean_eq hν_int n hn
  have h_sum_x : ∑ i, x i = (n : ℝ) * μ.expect id := by
    have h_mean_eq : (condMeanAtomize μ n hn).mean = (∑ i, x i) / n := by
      simpa only [hx_def, condMeanAtomize] using
        DiscreteLaw.uniform_mean hn (fun k => condMeanAtom μ n hn k)
    rw [hμ_mean] at h_mean_eq
    field_simp at h_mean_eq
    linarith
  have h_sum_y : ∑ i, y i = (n : ℝ) * ν.expect id := by
    have h_mean_eq : (condMeanAtomize ν n hn).mean = (∑ i, y i) / n := by
      simpa only [hy_def, condMeanAtomize] using
        DiscreteLaw.uniform_mean hn (fun k => condMeanAtom ν n hn k)
    rw [hν_mean] at h_mean_eq
    field_simp at h_mean_eq
    linarith
  have hsum : ∑ i, x i = ∑ i, y i := by
    rw [h_sum_x, h_sum_y, h.mean_eq]
  -- Partial-sum comparison: `∑_{i ≤ K} y i ≤ ∑_{i ≤ K} x i`.
  have hpart : ∀ K : Fin n,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), y i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), x i) := by
    intro K
    -- Use `condMeanAtomize_partial_sum_eq` for both μ and ν.
    have h_partial_μ :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), x i) =
          (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u := by
      simpa [hx_def] using condMeanAtomize_partial_sum_eq h.support_left hn K
    have h_partial_ν :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), y i) =
          (n : ℝ) * ∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile ν.toMeasure u := by
      simpa [hy_def] using condMeanAtomize_partial_sum_eq h.support_right hn K
    rw [h_partial_μ, h_partial_ν]
    -- Bound t = (K.val + 1)/n in (0, 1].
    have ht_pos : (0 : ℝ) < ((K.val + 1 : ℝ) / n) := by
      apply div_pos _ hn_pos_R
      have : (0 : ℕ) < K.val + 1 := Nat.succ_pos _
      exact_mod_cast this
    have ht_le_1 : ((K.val + 1 : ℝ) / n) ≤ 1 := by
      rw [div_le_one hn_pos_R]
      have hKlt : K.val + 1 ≤ n := K.isLt
      exact_mod_cast hKlt
    -- The lower integrated quantile of `ν` is dominated by that of `μ` under the convex order.
    have h_ineq :
        (∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile ν.toMeasure u) ≤
          (∫ u in Set.Ioc (0 : ℝ) ((K.val + 1 : ℝ) / n),
            MeasureTheory.Measure.quantile μ.toMeasure u) :=
      lowerIntegratedQuantile_ge_of_convexOrderOnIcc h ⟨ht_pos, ht_le_1⟩
    exact mul_le_mul_of_nonneg_left h_ineq hn_pos_R.le
  exact sum_convex_le_of_partial_sum_ge x y hx_mono hy_mono hsum hpart hφ

end DiscreteLaw
end Econlib.Probability

end
end

section
open MeasureTheory Set Filter Topology

namespace Econlib.Probability

/-- **Discrete approximation in convex order.** A pair `μ ≼cx[a,b] ν` of real-valued laws supported
on `[a, b]` admits a sequence of finitely-supported pairs `(pₙ, qₙ)` in convex order, with weak
convergence of the embedded laws to `μ` and `ν` respectively. -/
theorem exists_discrete_approximation {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) :
    ∃ p q : ℕ → DiscreteLaw,
      (∀ n, DiscreteLaw.ConvexOrder (p n) (q n)) ∧
      (∀ n, 0 < (p n).n) ∧
      (∀ n, (p n).n = (q n).n) ∧
      (∀ n i, (p n).weight i = (1 : ℝ) / (p n).n) ∧
      (∀ n j, (q n).weight j = (1 : ℝ) / (q n).n) ∧
      (∀ n i, (p n).atom i ∈ Icc a b) ∧
      (∀ n j, (q n).atom j ∈ Icc a b) ∧
      Tendsto (fun n => (p n).toProbDist : ℕ → ProbabilityMeasure ℝ) atTop (𝓝 μ) ∧
      Tendsto (fun n => (q n).toProbDist : ℕ → ProbabilityMeasure ℝ) atTop (𝓝 ν) := by
  refine ⟨fun n => DiscreteLaw.condMeanAtomize μ (n + 1) (Nat.succ_pos n),
          fun n => DiscreteLaw.condMeanAtomize ν (n + 1) (Nat.succ_pos n),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n =>
      DiscreteLaw.condMeanAtomize_convexOrder h (n + 1) (Nat.succ_pos n)
  · intro n
    simp [DiscreteLaw.condMeanAtomize, DiscreteLaw.uniform]
  · intro n
    simp [DiscreteLaw.condMeanAtomize, DiscreteLaw.uniform]
  · intro n i
    rfl
  · intro n j
    rfl
  · exact fun n i =>
      DiscreteLaw.condMeanAtom_mem_Icc h.support_left (n + 1) (Nat.succ_pos n) i
  · exact fun n j =>
      DiscreteLaw.condMeanAtom_mem_Icc h.support_right (n + 1) (Nat.succ_pos n) j
  · exact DiscreteLaw.condMeanAtomize_tendsto h.support_left
  · exact DiscreteLaw.condMeanAtomize_tendsto h.support_right

end Econlib.Probability
end
