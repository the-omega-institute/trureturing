/- GID: D5/S3/Analytic/Probability/CompactQuantile
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/CompactQuantile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: CompactQuantile for compact scalar martingale transport. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.CDF


open MeasureTheory Set Filter Topology

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- Generalized inverse of the CDF: `t`-th quantile of `μ`. For `t ∈ (0, 1)` this is the smallest
`x` such that `F_μ(x) = (μ (Iic x)).toReal ≥ t`. Outside that range the definition may give junk. -/
def quantile (t : ℝ) : ℝ :=
  sInf { x : ℝ | t ≤ (μ (Iic x)).toReal }

variable {μ}

/-- For a probability measure, `F_μ = ↑(cdf μ)` agrees with `(μ (Iic ·)).toReal`. -/
private lemma cdf_eq_toReal_measure_Iic [IsProbabilityMeasure μ] (x : ℝ) :
    (ProbabilityTheory.cdf μ) x = (μ (Iic x)).toReal := by
  rw [ProbabilityTheory.cdf_eq_real]; rfl

/-- The coerced CDF is, as a function, `x ↦ (μ (Iic x)).toReal`. -/
private lemma cdf_coe_eq_toReal_measure_Iic [IsProbabilityMeasure μ] :
    ((ProbabilityTheory.cdf μ) : ℝ → ℝ) = fun x : ℝ => (μ (Iic x)).toReal :=
  funext cdf_eq_toReal_measure_Iic

/-- For a probability measure, the CDF `x ↦ (μ (Iic x)).toReal` tends to `1` at `+∞`. -/
private lemma tendsto_toReal_measure_Iic_atTop [IsProbabilityMeasure μ] :
    Tendsto (fun x : ℝ => (μ (Iic x)).toReal) atTop (𝓝 1) :=
  cdf_coe_eq_toReal_measure_Iic (μ := μ) ▸ ProbabilityTheory.tendsto_cdf_atTop μ

/-- For a probability measure, the CDF `x ↦ (μ (Iic x)).toReal` tends to `0` at `-∞`. -/
private lemma tendsto_toReal_measure_Iic_atBot [IsProbabilityMeasure μ] :
    Tendsto (fun x : ℝ => (μ (Iic x)).toReal) atBot (𝓝 0) :=
  cdf_coe_eq_toReal_measure_Iic (μ := μ) ▸ ProbabilityTheory.tendsto_cdf_atBot μ

/-- For a probability measure, the CDF is monotone. -/
private lemma monotone_toReal_measure_Iic [IsProbabilityMeasure μ] :
    Monotone (fun x : ℝ => (μ (Iic x)).toReal) := by
  intro x y hxy
  simp_rw [← cdf_eq_toReal_measure_Iic]
  exact ProbabilityTheory.monotone_cdf μ hxy

/-- For a probability measure, the CDF is right-continuous. -/
private lemma rightContinuous_toReal_measure_Iic [IsProbabilityMeasure μ] (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => (μ (Iic y)).toReal) (Ici x) x :=
  cdf_coe_eq_toReal_measure_Iic (μ := μ) ▸ (ProbabilityTheory.cdf μ).right_continuous x

/-- The CDF value `(μ (Iic x)).toReal` is nonnegative. -/
private lemma toReal_measure_Iic_nonneg (x : ℝ) : 0 ≤ (μ (Iic x)).toReal := ENNReal.toReal_nonneg

/-- For a probability measure, the CDF value `(μ (Iic x)).toReal` is at most `1`. -/
private lemma toReal_measure_Iic_le_one [IsProbabilityMeasure μ] (x : ℝ) :
    (μ (Iic x)).toReal ≤ 1 := by
  simp_rw [← cdf_eq_toReal_measure_Iic]
  exact ProbabilityTheory.cdf_le_one μ x

namespace Quantile

/-- For a probability measure and `t < 1`, the superlevel set of the CDF at height `t` is nonempty.
Follows from `(μ(Iic x)).toReal → 1` at `+∞`. -/
lemma set_nonempty [IsProbabilityMeasure μ] {t : ℝ} (ht_lt : t < 1) :
    ({ x : ℝ | t ≤ (μ (Iic x)).toReal }).Nonempty := by
  have h := tendsto_toReal_measure_Iic_atTop (μ := μ)
  have hε : 1 - t > 0 := by linarith
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1 - t) hε
  refine ⟨N, ?_⟩
  have h1 := hN N (le_refl _)
  rw [Real.dist_eq] at h1
  rw [abs_sub_lt_iff] at h1
  simp only [Set.mem_setOf_eq]; linarith

/-- For a probability measure and `0 < t`, the superlevel set of the CDF at height `t` is bounded
below. Follows from `(μ(Iic x)).toReal → 0` at `-∞`. -/
private lemma set_bddBelow [IsProbabilityMeasure μ] {t : ℝ} (ht_pos : 0 < t) :
    BddBelow { x : ℝ | t ≤ (μ (Iic x)).toReal } := by
  have h := tendsto_toReal_measure_Iic_atBot (μ := μ)
  -- Use Filter.tendsto_atBot characterization via eventual bounds.
  rw [Metric.tendsto_nhds] at h
  have := h t ht_pos
  -- `this : ∀ᶠ x in atBot, dist ((μ (Iic x)).toReal) 0 < t`
  rw [Filter.eventually_atBot] at this
  obtain ⟨N, hN⟩ := this
  refine ⟨N, ?_⟩
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_contra hxlt
  push Not at hxlt
  have hd := hN x hxlt.le
  rw [Real.dist_eq, sub_zero, abs_lt] at hd
  linarith [hd.2]

end Quantile

/-- Galois identity between the quantile and the CDF. For a probability measure and `t ∈ Ioo 0 1`,
`quantile μ t ≤ x ↔ t ≤ (μ (Iic x)).toReal`. -/
lemma quantile_le_iff [IsProbabilityMeasure μ] {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {x : ℝ} :
    quantile μ t ≤ x ↔ t ≤ (μ (Iic x)).toReal := by
  obtain ⟨ht_pos, ht_lt⟩ := ht
  refine ⟨fun h => ?_, fun h => csInf_le (Quantile.set_bddBelow ht_pos) h⟩
  -- Forward direction: use right-continuity of the CDF at `quantile μ t`.
  set c := quantile μ t with hc_def
  have h_inf_set := Quantile.set_nonempty (μ := μ) ht_lt
  have h_inf_bdd := Quantile.set_bddBelow (μ := μ) ht_pos
  -- `c` lies in the superlevel set: right-continuity carries `t ≤ F` from points just above `c`.
  have hc_in : t ≤ (μ (Iic c)).toReal := by
    -- Right-continuity at c: for every ε > 0, there's δ > 0 such that for y ∈ [c, c+δ),
    -- |F(y) - F(c)| < ε.  Meanwhile, by definition of sInf, for every δ > 0 there is y with
    -- c ≤ y < c + δ and t ≤ F(y).  Taking ε → 0 gives t ≤ F(c).
    have h_rc := rightContinuous_toReal_measure_Iic (μ := μ) c
    -- Use the equivalent ε-δ form.
    rw [Metric.continuousWithinAt_iff] at h_rc
    by_contra hnot
    push Not at hnot
    -- hnot : (μ (Iic c)).toReal < t
    have hε : t - (μ (Iic c)).toReal > 0 := by linarith
    obtain ⟨δ, hδ_pos, hδ⟩ := h_rc (t - (μ (Iic c)).toReal) hε
    -- By definition of sInf, there is y ∈ set with y < c + δ.
    have h_exists : ∃ y, y ∈ { x : ℝ | t ≤ (μ (Iic x)).toReal } ∧ y < c + δ := by
      by_contra hne
      push Not at hne
      -- Then c + δ is a lower bound, so c + δ ≤ sInf = c, contradicting δ > 0.
      have hlb : c + δ ≤ c := by
        apply le_csInf h_inf_set
        intro y hy
        have := hne y hy
        linarith
      linarith
    obtain ⟨y, hy_in, hy_lt⟩ := h_exists
    -- y ∈ set means t ≤ F(y).  Also c ≤ y since c is the inf.
    have hcy : c ≤ y := csInf_le h_inf_bdd hy_in
    -- Now use right-continuity: dist(F(y), F(c)) < ε.
    -- y ∈ Ici c since c ≤ y, and dist y c < δ since c ≤ y < c + δ.
    have hy_Ici : y ∈ Ici c := hcy
    have hdist : dist y c < δ := by
      rw [Real.dist_eq]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - c)]
      linarith
    have hFyc := hδ hy_Ici hdist
    -- hFyc : dist ((μ (Iic y)).toReal) ((μ (Iic c)).toReal) < t - (μ (Iic c)).toReal
    rw [Real.dist_eq] at hFyc
    rw [abs_lt] at hFyc
    have hy_in' : t ≤ (μ (Iic y)).toReal := hy_in
    linarith [hFyc.2]
  -- Monotonicity then carries `t ≤ F(c)` to `t ≤ F(x)` via `c ≤ x`.
  have hmono : (μ (Iic c)).toReal ≤ (μ (Iic x)).toReal :=
    monotone_toReal_measure_Iic h
  linarith

/-- The quantile function is monotone on `Ioo 0 1`. -/
lemma monotoneOn_quantile [IsProbabilityMeasure μ] :
    MonotoneOn (quantile μ) (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  -- Goal: quantile μ s ≤ quantile μ t.
  -- Use that quantile μ s ≤ x iff s ≤ F(x), and apply at x := quantile μ t.
  rw [quantile_le_iff hs]
  -- Goal: s ≤ (μ (Iic (quantile μ t))).toReal.
  have h_self : quantile μ t ≤ quantile μ t := le_refl _
  rw [quantile_le_iff ht] at h_self
  -- h_self : t ≤ (μ (Iic (quantile μ t))).toReal
  linarith

/-- The quantile function is AE-measurable with respect to `volume.restrict (Ioo 0 1)`. Follows
from `aemeasurable_restrict_of_monotoneOn`, since `quantile μ` is monotone on `Ioo 0 1`. -/
lemma aemeasurable_quantile_restrict_Ioo [IsProbabilityMeasure μ] :
    AEMeasurable (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo monotoneOn_quantile

section Pushforward

variable [IsProbabilityMeasure μ]

/-- Key computation: Volume of `{t ∈ Ioo 0 1 | t ≤ a}` when `0 ≤ a ≤ 1`. -/
private lemma volume_Ioo_inter_Iic {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic a) = ENNReal.ofReal a := by
  -- Case analysis: if `a = 1`, the intersection is `Ioo 0 1` (volume 1).
  -- Otherwise `a < 1`, the intersection is `Ioc 0 a` (volume `a`).
  rcases eq_or_lt_of_le ha1 with ha1_eq | ha1_lt
  · -- a = 1
    subst ha1_eq
    have h_eq : Ioo (0 : ℝ) 1 ∩ Iic 1 = Ioo (0 : ℝ) 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ioo, mem_Iic]
      constructor
      · exact fun h => h.1
      · intro hx; exact ⟨hx, hx.2.le⟩
    rw [h_eq, Real.volume_Ioo]; ring_nf
  · -- a < 1
    have h_eq : Ioo (0 : ℝ) 1 ∩ Iic a = Ioc 0 a := by
      ext x
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨hx0, _⟩, hxa⟩; exact ⟨hx0, hxa⟩
      · rintro ⟨hx0, hxa⟩; exact ⟨⟨hx0, by linarith⟩, hxa⟩
    rw [h_eq, Real.volume_Ioc]; ring_nf

/-- The pushforward of `volume.restrict (Ioo 0 1)` under `quantile μ`, evaluated on `Iic x`, equals
`μ (Iic x)`. -/
private lemma map_quantile_apply_Iic (x : ℝ) :
    (Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1))) (Iic x) = μ (Iic x) := by
  -- First rewrite via `map_apply_of_aemeasurable`.
  rw [Measure.map_apply_of_aemeasurable aemeasurable_quantile_restrict_Ioo measurableSet_Iic]
  -- Goal: (volume.restrict (Ioo 0 1)) (quantile μ ⁻¹' Iic x) = μ (Iic x).
  rw [Measure.restrict_apply' measurableSet_Ioo]
  -- Goal: volume (quantile μ ⁻¹' Iic x ∩ Ioo 0 1) = μ (Iic x).
  -- We'll show this set equals `Ioo 0 1 ∩ Iic F_μ(x)` and apply `volume_Ioo_inter_Iic`.
  set a := (μ (Iic x)).toReal with ha_def
  have ha0 : 0 ≤ a := toReal_measure_Iic_nonneg x
  have ha1 : a ≤ 1 := toReal_measure_Iic_le_one x
  have h_eq : quantile μ ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 ∩ Iic a := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
    constructor
    · rintro ⟨hqt, ht⟩
      refine ⟨ht, ?_⟩
      exact (quantile_le_iff ht).mp hqt
    · rintro ⟨ht, hta⟩
      exact ⟨(quantile_le_iff ht).mpr hta, ht⟩
  rw [h_eq, volume_Ioo_inter_Iic ha0 ha1]
  -- Goal: ENNReal.ofReal a = μ (Iic x). We use `ofReal_cdf`.
  have h_cdf : ENNReal.ofReal ((ProbabilityTheory.cdf μ) x) = μ (Iic x) :=
    ProbabilityTheory.ofReal_cdf μ x
  rw [← h_cdf, ha_def, cdf_eq_toReal_measure_Iic]

/-- **Pushforward identity.** The image measure of `volume.restrict (Ioo 0 1)` under the quantile
function `quantile μ` is `μ`. -/
theorem map_quantile_volume_Ioo :
    Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) = μ := by
  -- Apply extensionality on `Iic`.
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  exact map_quantile_apply_Iic x

end Pushforward

/-- Change-of-variables identity for the quantile pushforward: The integral of `φ` against `μ`
equals the integral of `φ ∘ quantile μ` against Lebesgue measure on `Ioo 0 1`.

This is the *total* Bochner-integral formulation — both sides are total integrals — and it holds
under only `AEStronglyMeasurable φ μ`, with no integrability hypothesis. (For non-integrable `φ`
both total integrals are `0`, so the equality is not an expectation-preserving statement; read it
as change of variables for the total integral.) -/
theorem integral_eq_integral_quantile [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ℝ → E)
    (hφ : AEStronglyMeasurable φ μ) :
    ∫ x, φ x ∂μ = ∫ t in Ioo (0 : ℝ) 1, φ (quantile μ t) := by
  -- Use the pushforward identity and `integral_map`.
  conv_lhs => rw [← map_quantile_volume_Ioo (μ := μ)]
  rw [MeasureTheory.integral_map aemeasurable_quantile_restrict_Ioo]
  -- After the rewrite, the AEStronglyMeasurable hypothesis on φ is against the pushforward,
  -- which equals μ.
  rw [map_quantile_volume_Ioo (μ := μ)]
  exact hφ

end MeasureTheory.Measure

end
end

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace MeasureTheory.Measure

variable {μ : Measure ℝ}

/-- The midpoint function for the uniform partition of size `n`. -/
def binMidpoint (n : ℕ) (t : ℝ) : ℝ := ((⌊(n : ℝ) * t⌋₊ : ℝ) + 1 / 2) / n

/-- On `[0, 1)`, the midpoint is within `1/n` of `t`. -/
-- `_ht1` unused: the bound only needs the floor sandwich, not `t < 1`; kept to match
-- `binMidpoint_mem_Ioo`'s hypotheses.
private lemma abs_binMidpoint_sub_le {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (_ht1 : t < 1) :
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
private lemma binMidpoint_mem_Ioo {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
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
private lemma binMidpoint_eq_of_mem_Ico {n : ℕ} (hn : 1 ≤ n) (k : Fin n) {t : ℝ}
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

/-- Step function: `stepFun μ φ n t = φ (quantile μ (binMidpoint n t))`. -/
def stepFun (μ : Measure ℝ) (φ : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  φ (quantile μ (binMidpoint n t))

/-- On each bin, `stepFun` is the constant `φ (quantile μ ((k + 1/2) / n))`. -/
private lemma stepFun_eq_of_mem_Ico {μ : Measure ℝ} {φ : ℝ → ℝ} {n : ℕ} (hn : 1 ≤ n) (k : Fin n)
    {t : ℝ} (ht : t ∈ Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)) :
    stepFun μ φ n t = φ (quantile μ (((k : ℝ) + 1 / 2) / n)) := by
  unfold stepFun
  rw [binMidpoint_eq_of_mem_Ico hn k ht]

/-- The step function is bounded by `M` whenever `|φ| ≤ M`. -/
private lemma abs_stepFun_le {μ : Measure ℝ} {φ : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |φ x| ≤ M)
    (n : ℕ) (t : ℝ) : |stepFun μ φ n t| ≤ M := by
  unfold stepFun
  exact hM _

/-- The step function is AE-strongly-measurable on `Ioo 0 1`, for continuous `φ`. -/
-- `_hφ` unused: `stepFun` is a finite sum of indicators of constants, measurable regardless of
-- `φ`'s continuity; kept so the hypothesis matches `integral_stepFun_Ioo`.
private lemma aestronglyMeasurable_stepFun {φ : ℝ → ℝ} (_hφ : Continuous φ) (n : ℕ) :
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
private lemma integral_stepFun_Ioo {φ : ℝ → ℝ} (_hφ : Continuous φ) {n : ℕ} (hn : 1 ≤ n) :
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

/-- For `t ∈ Ioo 0 1` where `quantile μ` is continuous within `Ioo 0 1` at `t`, the step function
value `stepFun μ φ n t` converges to `φ (quantile μ t)` as `n → ∞`. -/
private lemma tendsto_stepFun_of_continuousWithinAt {φ : ℝ → ℝ} (hφ : Continuous φ)
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
private lemma stepFun_tendsto_ae [IsProbabilityMeasure μ] {φ : ℝ → ℝ} (hφ : Continuous φ) :
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

/-- The constant `M` is integrable on `Ioo 0 1` (a finite-measure set). -/
private lemma integrable_const_Ioo (M : ℝ) :
    Integrable (fun _ : ℝ => M) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  refine integrable_const _

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
end

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- **Stop-loss function.** `stopLoss μ z = ∫ max (x - z) 0 ∂μ`, the totalized Bochner integral of
the hinge `(x - z)⁺` against an arbitrary measure `μ`. When `x ↦ (x - z)⁺` is `μ`-integrable (e.g.
`μ` a probability measure with finite first moment) this is the expected overshoot of `X ∼ μ` above
the threshold `z`; otherwise the Bochner integral returns `0`. -/
def stopLoss (z : ℝ) : ℝ := ∫ x, max (x - z) 0 ∂μ

variable {μ}

/-- Non-negativity of the stop-loss. -/
lemma stopLoss_nonneg (z : ℝ) : 0 ≤ stopLoss μ z :=
  integral_nonneg (fun _ => le_max_right _ _)

/-- If `x ↦ x` is `μ`-integrable (finite first moment), then `x ↦ max (x - z) 0` is integrable
too. -/
lemma stopLoss_integrable [IsFiniteMeasure μ] (hμ : Integrable (fun x : ℝ => x) μ) (z : ℝ) :
    Integrable (fun x : ℝ => max (x - z) 0) μ := by
  have h1 : Integrable (fun x : ℝ => x - z) μ := hμ.sub (integrable_const z)
  have h2 : Integrable (fun _ : ℝ => (0 : ℝ)) μ := integrable_const 0
  exact h1.sup h2

end MeasureTheory.Measure

end
end
