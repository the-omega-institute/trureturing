/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.CDF

/-!
# Quantile Function of a Probability Measure on ℝ

The **quantile function** (generalized inverse of the CDF) of a probability measure `μ` on ℝ is

`quantile μ t = sInf { x : ℝ | t ≤ μ(Iic x).toReal }`.

For `t ∈ (0, 1)` it is the smallest real `x` with `F_μ(x) ≥ t`, where `F_μ(x) = μ((-∞, x])`.

## Main definitions

* `Measure.quantile` — the **quantile function** `t ↦ sInf { x | t ≤ F_μ(x) }`.

## Main statements

* `Measure.quantile_le_iff` — **Galois identity** `quantile μ t ≤ x ↔ t ≤ F_μ(x)` for `t ∈ (0, 1)`.
* `Measure.monotoneOn_quantile` — `quantile μ` is monotone on `(0, 1)`.
* `Measure.aemeasurable_quantile_restrict_Ioo` — AE-measurability on `Ioo 0 1`.
* `Measure.map_quantile_volume_Ioo` — the pushforward of `volume.restrict (Ioo 0 1)` under the
  quantile function is `μ`.
* `Measure.integral_eq_integral_quantile` — change of variables
  `∫ φ dμ = ∫ t in Ioo 0 1, φ (quantile μ t)`.

## Notes

The pushforward identity holds for every probability measure; no atomlessness is required, since
the quantile transform realizes `μ` as the image of Lebesgue measure on `(0, 1)`.

## Tags

quantile, generalized inverse, cumulative distribution function, change of variables
-/

@[expose] public section

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
lemma cdf_eq_toReal_measure_Iic [IsProbabilityMeasure μ] (x : ℝ) :
    (ProbabilityTheory.cdf μ) x = (μ (Iic x)).toReal := by
  rw [ProbabilityTheory.cdf_eq_real]; rfl

/-- The coerced CDF is, as a function, `x ↦ (μ (Iic x)).toReal`. -/
lemma cdf_coe_eq_toReal_measure_Iic [IsProbabilityMeasure μ] :
    ((ProbabilityTheory.cdf μ) : ℝ → ℝ) = fun x : ℝ => (μ (Iic x)).toReal :=
  funext cdf_eq_toReal_measure_Iic

/-- For a probability measure, the CDF `x ↦ (μ (Iic x)).toReal` tends to `1` at `+∞`. -/
lemma tendsto_toReal_measure_Iic_atTop [IsProbabilityMeasure μ] :
    Tendsto (fun x : ℝ => (μ (Iic x)).toReal) atTop (𝓝 1) :=
  cdf_coe_eq_toReal_measure_Iic (μ := μ) ▸ ProbabilityTheory.tendsto_cdf_atTop μ

/-- For a probability measure, the CDF `x ↦ (μ (Iic x)).toReal` tends to `0` at `-∞`. -/
lemma tendsto_toReal_measure_Iic_atBot [IsProbabilityMeasure μ] :
    Tendsto (fun x : ℝ => (μ (Iic x)).toReal) atBot (𝓝 0) :=
  cdf_coe_eq_toReal_measure_Iic (μ := μ) ▸ ProbabilityTheory.tendsto_cdf_atBot μ

/-- For a probability measure, the CDF is monotone. -/
lemma monotone_toReal_measure_Iic [IsProbabilityMeasure μ] :
    Monotone (fun x : ℝ => (μ (Iic x)).toReal) := by
  intro x y hxy
  simp_rw [← cdf_eq_toReal_measure_Iic]
  exact ProbabilityTheory.monotone_cdf μ hxy

/-- For a probability measure, the CDF is right-continuous. -/
lemma rightContinuous_toReal_measure_Iic [IsProbabilityMeasure μ] (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => (μ (Iic y)).toReal) (Ici x) x :=
  cdf_coe_eq_toReal_measure_Iic (μ := μ) ▸ (ProbabilityTheory.cdf μ).right_continuous x

/-- The CDF value `(μ (Iic x)).toReal` is nonnegative. -/
lemma toReal_measure_Iic_nonneg (x : ℝ) : 0 ≤ (μ (Iic x)).toReal := ENNReal.toReal_nonneg

/-- For a probability measure, the CDF value `(μ (Iic x)).toReal` is at most `1`. -/
lemma toReal_measure_Iic_le_one [IsProbabilityMeasure μ] (x : ℝ) :
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
lemma set_bddBelow [IsProbabilityMeasure μ] {t : ℝ} (ht_pos : 0 < t) :
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

/-! ### Pushforward of Lebesgue measure on `Ioo 0 1` under `quantile μ` equals `μ`. -/

section Pushforward

variable [IsProbabilityMeasure μ]

/-- Lebesgue measure of `Ioo 0 1` is `1`. -/
private lemma volume_Ioo_0_1 : volume (Ioo (0 : ℝ) 1) = 1 := by
  rw [Real.volume_Ioo]; simp

/-- The restriction of Lebesgue measure to `Ioo 0 1` is a probability measure. -/
instance : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact volume_Ioo_0_1

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
  -- The pushforward is a probability measure since `volume.restrict (Ioo 0 1)` is,
  -- and `quantile μ` is AE-measurable.
  haveI : IsProbabilityMeasure
      (Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1))) :=
    (Measure.isProbabilityMeasure_map_iff aemeasurable_quantile_restrict_Ioo).mpr inferInstance
  -- Apply extensionality on `Iic`.
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  exact map_quantile_apply_Iic x

end Pushforward

/-! ### Integral change of variables. -/

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
