/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.Order.Strassen.Basic
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Probability.ProbDist.WeakTopology
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Weak limits of martingale couplings

This file proves weak-limit stability for **martingale couplings**. Given a sequence of couplings
`πₙ` whose marginals concentrate on a fixed compact interval and whose marginal laws converge
weakly to `μ, ν`, every weak limit `π` is again a martingale coupling of `(μ, ν)`. The tested
martingale identity passes to the limit first for bounded continuous test functions and is then
lifted to bounded measurable ones.

## Main statements

* `tested_martingale_of_weak_limit` — the tested martingale identity for bounded continuous `φ`
  passes to a weak limit of couplings concentrated on `Icc a b × Icc a b`.
* `tested_martingale_measurable_of_continuous` — the tested identity for bounded continuous `φ`
  lifts to bounded measurable `φ`.
* `IsMartingaleCoupling.of_weak_limit` — every weak limit point of a sequence of martingale
  couplings concentrated on `Icc a b × Icc a b`, with marginals converging weakly to `μ, ν`, is a
  martingale coupling of `(μ, ν)`.

## References

* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).

## Tags

strassen, martingale coupling, weak convergence, lévy–prokhorov, tightness
-/
open MeasureTheory Set Filter Topology
open scoped ENNReal

@[expose] public section

namespace Econlib.Probability

/-- **Tested martingale identity passes to the weak limit (continuous φ).** If each `πₙ` is a
martingale coupling concentrated on `Icc a b × Icc a b`, then any weak limit has the tested
identity for every bounded continuous `φ`. -/
lemma tested_martingale_of_weak_limit {a b : ℝ}
    {π_seq : ℕ → ProbDist (ℝ × ℝ)} {πInf : ProbDist (ℝ × ℝ)}
    (hπsupp : ∀ n, (π_seq n).toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hInfSupp : πInf.toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hπmart : ∀ n, ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂(π_seq n).toMeasure = 0)
    (hπlim : Tendsto (fun n => (π_seq n : ProbabilityMeasure (ℝ × ℝ))) atTop (𝓝 πInf))
    (φ : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M) :
    ∫ p, (p.2 - p.1) * φ p.1 ∂πInf.toMeasure = 0 := by
  -- Extract `a ≤ b` from the support hypothesis; otherwise `Icc a b = ∅` but
  -- `πInf (Icc a b × Icc a b) = 1 ≠ 0`.
  have hab : a ≤ b := by
    by_contra hab'
    rw [Set.Icc_eq_empty hab'] at hInfSupp
    simp at hInfSupp
  -- Build a bounded continuous ψ : ℝ × ℝ → ℝ that equals (y - x) * φ(x) on Icc × Icc.
  -- Let `c : ℝ → ℝ` be the clamp `x ↦ max a (min b x)` (Set.projIcc applied).
  set c : ℝ → ℝ := fun x => max a (min b x) with hc_def
  have hc_cont : Continuous c :=
    (continuous_const.max (continuous_const.min continuous_id))
  have hc_mem : ∀ x, c x ∈ Icc a b := fun x =>
    ⟨le_max_left a _, max_le hab (min_le_left b x)⟩
  have hc_id_on_Icc : ∀ x ∈ Icc a b, c x = x := by
    rintro x ⟨hxa, hxb⟩
    simp only [hc_def]
    have hmin : min b x = x := min_eq_right hxb
    rw [hmin, max_eq_right hxa]
  -- Define ψ := (c ∘ snd - c ∘ fst) * (φ ∘ c ∘ fst).
  set ψ : ℝ × ℝ → ℝ := fun p => (c p.2 - c p.1) * φ (c p.1) with hψ_def
  have hψ_cont : Continuous ψ := by
    refine Continuous.mul ?_ ?_
    · exact (hc_cont.comp continuous_snd).sub (hc_cont.comp continuous_fst)
    · exact hφ_cont.comp (hc_cont.comp continuous_fst)
  -- ψ is bounded: |c(y) - c(x)| ≤ b - a ≥ 0, and |φ(c(x))| ≤ M.
  obtain ⟨M, hM⟩ := hφ_bdd
  have hψ_bdd : ∀ p, |ψ p| ≤ (b - a) * M := by
    intro p
    have h1 : |c p.2 - c p.1| ≤ b - a := by
      have hcx := hc_mem p.1
      have hcy := hc_mem p.2
      rcases le_or_gt (c p.2) (c p.1) with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]
        have : c p.1 - c p.2 ≤ b - a := sub_le_sub hcx.2 hcy.1
        linarith
      · rw [abs_of_pos (sub_pos.mpr h)]
        exact sub_le_sub hcy.2 hcx.1
    have h2 : |φ (c p.1)| ≤ M := hM (c p.1)
    calc |ψ p| = |c p.2 - c p.1| * |φ (c p.1)| := by rw [hψ_def]; exact abs_mul _ _
      _ ≤ (b - a) * M := by
          have hM0 : 0 ≤ M := le_trans (abs_nonneg _) h2
          have hba0 : 0 ≤ b - a := by linarith
          exact mul_le_mul h1 h2 (abs_nonneg _) hba0
  -- Bounded continuous version as `BoundedContinuousFunction`.
  let ψBC : BoundedContinuousFunction (ℝ × ℝ) ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨ψ, hψ_cont⟩ (2 * ((b - a) * M)) (by
        intro p q
        have hp := hψ_bdd p
        have hq := hψ_bdd q
        calc dist (ψ p) (ψ q) = |ψ p - ψ q| := by rw [Real.dist_eq]
          _ ≤ |ψ p| + |ψ q| := abs_sub _ _
          _ ≤ (b - a) * M + (b - a) * M := add_le_add hp hq
          _ = 2 * ((b - a) * M) := by ring)
  -- On the compact square, ψ equals (y - x) * φ(x).
  have hψ_eq : ∀ p ∈ Icc a b ×ˢ Icc a b, ψ p = (p.2 - p.1) * φ p.1 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [hψ_def, hc_id_on_Icc x hx, hc_id_on_Icc y hy]
  -- Convert: `∫ ψ dπ = ∫ (y - x) * φ x dπ` whenever π is concentrated on the square.
  have hint_eq : ∀ (ρ : Measure (ℝ × ℝ)) (_hρ : ρ (Icc a b ×ˢ Icc a b) = 1)
      [_hρprob : IsProbabilityMeasure ρ],
      ∫ p, ψ p ∂ρ = ∫ p, (p.2 - p.1) * φ p.1 ∂ρ := by
    intro ρ hρ _
    refine MeasureTheory.integral_congr_ae ?_
    have hmeas : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
      measurableSet_Icc.prod measurableSet_Icc
    have : ∀ᵐ p ∂ρ, p ∈ Icc a b ×ˢ Icc a b := by
      rw [ae_iff]
      have hcompl : ρ (Icc a b ×ˢ Icc a b)ᶜ = 0 :=
        (MeasureTheory.prob_compl_eq_zero_iff hmeas).mpr hρ
      exact hcompl
    filter_upwards [this] with p hp
    exact hψ_eq p hp
  -- Apply the weak convergence on bounded continuous ψBC.
  have hconv :=
    (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hπlim) ψBC
  -- Each LHS is 0 via the martingale identity and support-based equality.
  have hzero : ∀ n, ∫ p, ψBC p ∂((π_seq n : ProbabilityMeasure (ℝ × ℝ)) :
      Measure (ℝ × ℝ)) = 0 := by
    intro n
    rw [show (fun p => ψBC p) = ψ from rfl,
      hint_eq ((π_seq n : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) (hπsupp n)]
    exact hπmart n (fun x => φ x) hφ_cont.measurable ⟨M, hM⟩
  have hconv0 : Tendsto
      (fun n => ∫ p, ψBC p ∂((π_seq n : ProbabilityMeasure (ℝ × ℝ)) :
        Measure (ℝ × ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n => (hzero n).symm
  -- Unique limit: `∫ ψ dπInf = 0`.
  have heq := tendsto_nhds_unique hconv hconv0
  -- Convert back to `∫ (y - x) * φ x dπInf = 0`.
  have hψBC_eq : (fun p => ψBC p) = ψ := rfl
  rw [hψBC_eq] at heq
  rw [← hint_eq πInf.toMeasure hInfSupp]
  exact heq

/-- **Tested martingale identity lifts to measurable φ.** If the tested identity holds for every
bounded continuous `φ` against a coupling concentrated on a compact square, then it holds for every
bounded measurable `φ`. -/
lemma tested_martingale_measurable_of_continuous {a b : ℝ} {π : ProbDist (ℝ × ℝ)}
    (_hsupp : π.toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hint_fst : Integrable (fun p : ℝ × ℝ => p.1) π.toMeasure)
    (hint_snd : Integrable (fun p : ℝ × ℝ => p.2) π.toMeasure)
    (hcts : ∀ φ : ℝ → ℝ, Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0) :
    ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0 := by
  -- Integrability of `p.2 - p.1` and `|p.2 - p.1|`.
  have h_diff_int : Integrable (fun p : ℝ × ℝ => p.2 - p.1) π.toMeasure :=
    hint_snd.sub hint_fst
  have h_abs_int : Integrable (fun p : ℝ × ℝ => |p.2 - p.1|) π.toMeasure := h_diff_int.abs
  -- NNReal-valued positive and negative parts of `p.2 - p.1`.
  let posW : ℝ × ℝ → NNReal := fun p => Real.toNNReal (p.2 - p.1)
  let negW : ℝ × ℝ → NNReal := fun p => Real.toNNReal (-(p.2 - p.1))
  have hposW_meas : Measurable posW :=
    (measurable_snd.sub measurable_fst).real_toNNReal
  have hnegW_meas : Measurable negW :=
    ((measurable_snd.sub measurable_fst).neg).real_toNNReal
  -- Real coercions of posW/negW as ℝ-valued non-negative functions.
  have h_pos_coe : ∀ p : ℝ × ℝ, ((posW p : ℝ)) = max (p.2 - p.1) 0 := by
    intro p; exact Real.coe_toNNReal' _
  have h_neg_coe : ∀ p : ℝ × ℝ, ((negW p : ℝ)) = max (-(p.2 - p.1)) 0 := by
    intro p; exact Real.coe_toNNReal' _
  have h_decomp : ∀ p : ℝ × ℝ, (posW p : ℝ) - (negW p : ℝ) = p.2 - p.1 := by
    intro p; rw [h_pos_coe, h_neg_coe]; exact max_zero_sub_eq_self _
  -- Pointwise bound: posW, negW ≤ |p.2 - p.1|.
  have h_pos_le_abs : ∀ p : ℝ × ℝ, (posW p : ℝ) ≤ |p.2 - p.1| := by
    intro p; rw [h_pos_coe]; exact max_le (le_abs_self _) (abs_nonneg _)
  have h_neg_le_abs : ∀ p : ℝ × ℝ, (negW p : ℝ) ≤ |p.2 - p.1| := by
    intro p; rw [h_neg_coe]; exact max_le (neg_le_abs _) (abs_nonneg _)
  -- Integrability of posW and negW (as ℝ-valued).
  have hposW_int : Integrable (fun p => (posW p : ℝ)) π.toMeasure := by
    refine h_abs_int.mono' ?_ ?_
    · exact (hposW_meas.coe_nnreal_real).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((posW p).coe_nonneg)]; exact h_pos_le_abs p)
  have hnegW_int : Integrable (fun p => (negW p : ℝ)) π.toMeasure := by
    refine h_abs_int.mono' ?_ ?_
    · exact (hnegW_meas.coe_nnreal_real).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((negW p).coe_nonneg)]; exact h_neg_le_abs p)
  -- ENNReal densities for `withDensity`.
  let posE : ℝ × ℝ → ENNReal := fun p => (posW p : ENNReal)
  let negE : ℝ × ℝ → ENNReal := fun p => (negW p : ENNReal)
  have hposE_meas : Measurable posE := hposW_meas.coe_nnreal_ennreal
  have hnegE_meas : Measurable negE := hnegW_meas.coe_nnreal_ennreal
  -- Finiteness of positive-part lintegral.
  have hposE_lint_ne : ∫⁻ p, posE p ∂π.toMeasure ≠ ⊤ := by
    have : ∫⁻ p, posE p ∂π.toMeasure = ENNReal.ofReal (∫ p, (posW p : ℝ) ∂π.toMeasure) := by
      rw [ofReal_integral_eq_lintegral_ofReal hposW_int
        (Filter.Eventually.of_forall (fun p => (posW p).coe_nonneg))]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      change (posW p : ENNReal) = ENNReal.ofReal ((posW p : ℝ))
      rw [ENNReal.ofReal_coe_nnreal]
    rw [this]; exact ENNReal.ofReal_ne_top
  have hnegE_lint_ne : ∫⁻ p, negE p ∂π.toMeasure ≠ ⊤ := by
    have : ∫⁻ p, negE p ∂π.toMeasure = ENNReal.ofReal (∫ p, (negW p : ℝ) ∂π.toMeasure) := by
      rw [ofReal_integral_eq_lintegral_ofReal hnegW_int
        (Filter.Eventually.of_forall (fun p => (negW p).coe_nonneg))]
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      change (negW p : ENNReal) = ENNReal.ofReal ((negW p : ℝ))
      rw [ENNReal.ofReal_coe_nnreal]
    rw [this]; exact ENNReal.ofReal_ne_top
  -- Finiteness instances for the weighted measures.
  haveI h_pos_fin : IsFiniteMeasure (π.toMeasure.withDensity posE) :=
    isFiniteMeasure_withDensity hposE_lint_ne
  haveI h_neg_fin : IsFiniteMeasure (π.toMeasure.withDensity negE) :=
    isFiniteMeasure_withDensity hnegE_lint_ne
  -- Pushforwards to ℝ via Prod.fst are finite measures too.
  let μ_pos : MeasureTheory.Measure ℝ := (π.toMeasure.withDensity posE).map Prod.fst
  let μ_neg : MeasureTheory.Measure ℝ := (π.toMeasure.withDensity negE).map Prod.fst
  haveI : IsFiniteMeasure μ_pos := Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure μ_neg := Measure.isFiniteMeasure_map _ _
  -- Integral identity: `∫ g dμ_pos = ∫ g(p.1) · (posW p : ℝ) dπ`, for any bounded measurable
  -- `g` (via `integral_map` + `integral_withDensity_eq_integral_smul`).
  have int_pos : ∀ (g : ℝ → ℝ) (_ : AEStronglyMeasurable g μ_pos),
      ∫ x, g x ∂μ_pos = ∫ p, (posW p : ℝ) * g (p.1) ∂π.toMeasure := by
    intro g hg
    change ∫ x, g x ∂((π.toMeasure.withDensity posE).map Prod.fst) = _
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable hg]
    -- Now LHS: ∫ (g ∘ Prod.fst) d(π.withDensity posE).
    rw [integral_withDensity_eq_integral_smul hposW_meas]
    -- Now: ∫ (posW p) • g(p.1) dπ = ∫ (posW p : ℝ) * g(p.1) dπ
    simp only [smul_eq_mul, NNReal.smul_def]
  have int_neg : ∀ (g : ℝ → ℝ) (_ : AEStronglyMeasurable g μ_neg),
      ∫ x, g x ∂μ_neg = ∫ p, (negW p : ℝ) * g (p.1) ∂π.toMeasure := by
    intro g hg
    change ∫ x, g x ∂((π.toMeasure.withDensity negE).map Prod.fst) = _
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable hg]
    rw [integral_withDensity_eq_integral_smul hnegW_meas]
    simp only [smul_eq_mul, NNReal.smul_def]
  -- Helper: integrability of `(posW p : ℝ) * φ(p.1)` for bounded measurable `φ`.
  have int_weighted_pos : ∀ (φ : ℝ → ℝ), Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      Integrable (fun p => (posW p : ℝ) * φ p.1) π.toMeasure := by
    intro φ hφ_meas hφ_bdd
    obtain ⟨M, hM⟩ := hφ_bdd
    have h1 : Integrable (fun p => φ p.1 * (posW p : ℝ)) π.toMeasure :=
      hposW_int.bdd_mul ((hφ_meas.comp measurable_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hM _))
    exact h1.congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  have int_weighted_neg : ∀ (φ : ℝ → ℝ), Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      Integrable (fun p => (negW p : ℝ) * φ p.1) π.toMeasure := by
    intro φ hφ_meas hφ_bdd
    obtain ⟨M, hM⟩ := hφ_bdd
    have h1 : Integrable (fun p => φ p.1 * (negW p : ℝ)) π.toMeasure :=
      hnegW_int.bdd_mul ((hφ_meas.comp measurable_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hM _))
    exact h1.congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  -- Splitting `p.2 - p.1` into its two non-negative parts collapses the difference of
  -- the weighted integrals into the single tested integral, for any bounded measurable `g`.
  have h_sub_gen : ∀ (g : ℝ → ℝ), Measurable g → (∃ M, ∀ x, |g x| ≤ M) →
      ∫ p, (posW p : ℝ) * g p.1 ∂π.toMeasure -
        ∫ p, (negW p : ℝ) * g p.1 ∂π.toMeasure =
        ∫ p, (p.2 - p.1) * g p.1 ∂π.toMeasure := by
    intro g hg_meas hg_bdd
    have h_cong : (fun p => (posW p : ℝ) * g p.1 - (negW p : ℝ) * g p.1) =
        fun p => (p.2 - p.1) * g p.1 := by
      funext p; rw [← sub_mul, h_decomp]
    rw [← MeasureTheory.integral_sub (int_weighted_pos g hg_meas hg_bdd)
      (int_weighted_neg g hg_meas hg_bdd), ← h_cong]
  -- Step: `μ_pos = μ_neg` via bounded-continuous extensionality.
  have hμ_eq : μ_pos = μ_neg := by
    refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
    have hf_cts : Continuous (f : ℝ → ℝ) := f.continuous
    have hf_bdd : ∃ M, ∀ x, |(f : ℝ → ℝ) x| ≤ M :=
      ⟨‖f‖, fun x => (Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm x⟩
    have hf_meas : Measurable (f : ℝ → ℝ) := hf_cts.measurable
    have hf_aesm : AEStronglyMeasurable (f : ℝ → ℝ) μ_pos :=
      hf_cts.aestronglyMeasurable
    have hf_aesm' : AEStronglyMeasurable (f : ℝ → ℝ) μ_neg :=
      hf_cts.aestronglyMeasurable
    rw [int_pos (f : ℝ → ℝ) hf_aesm, int_neg (f : ℝ → ℝ) hf_aesm']
    -- The difference of weighted integrals is the tested integral, which vanishes by `hcts`.
    have h_sub := h_sub_gen (f : ℝ → ℝ) hf_meas hf_bdd
    have h_ct := hcts (f : ℝ → ℝ) hf_cts hf_bdd
    linarith
  -- Conclusion: for measurable bounded `φ`, translate back via `hμ_eq` + `int_pos`/`int_neg`.
  intro φ hφ_meas hφ_bdd
  obtain ⟨M, hM⟩ := hφ_bdd
  have hφ_aesm_pos : AEStronglyMeasurable φ μ_pos := hφ_meas.aestronglyMeasurable
  have hφ_aesm_neg : AEStronglyMeasurable φ μ_neg := hφ_meas.aestronglyMeasurable
  have heq : ∫ x, φ x ∂μ_pos = ∫ x, φ x ∂μ_neg := by rw [hμ_eq]
  rw [int_pos φ hφ_aesm_pos, int_neg φ hφ_aesm_neg] at heq
  -- heq: ∫ (posW p) * φ(p.1) dπ = ∫ (negW p) * φ(p.1) dπ; subtract to get the tested integral.
  have h_sub := h_sub_gen φ hφ_meas ⟨M, hM⟩
  linarith

/-- **Main weak-limit theorem for martingale couplings.** Given a sequence
`πₙ : IsMartingaleCoupling μₙ νₙ πₙ` with all `πₙ` concentrated on `Icc a b × Icc a b` and
marginals converging weakly to `μ, ν`, every weak limit point of `πₙ` is a martingale coupling of
`(μ, ν)`. -/
theorem IsMartingaleCoupling.of_weak_limit {a b : ℝ}
    {μ ν : ProbDist ℝ} {μ_seq ν_seq : ℕ → ProbDist ℝ}
    {π_seq : ℕ → ProbDist (ℝ × ℝ)} {πInf : ProbDist (ℝ × ℝ)}
    (_hμ_supp : μ.supportsOn (Icc a b)) (_hν_supp : ν.supportsOn (Icc a b))
    (hπcoup : ∀ n, IsMartingaleCoupling (μ_seq n) (ν_seq n) (π_seq n))
    (hπsupp : ∀ n, (π_seq n).toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hInfSupp : πInf.toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hπlim : Tendsto (fun n => (π_seq n : ProbabilityMeasure (ℝ × ℝ))) atTop (𝓝 πInf))
    (hμlim : Tendsto (fun n => (μ_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 μ))
    (hνlim : Tendsto (fun n => (ν_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 ν)) :
    IsMartingaleCoupling μ ν πInf := by
  -- Step 1: marginals via `IsCoupling.of_weak_limit`.
  have hπcoup' : ∀ n, IsCoupling (μ_seq n) (ν_seq n) (π_seq n) := fun n =>
    ⟨(hπcoup n).fst_marginal, (hπcoup n).snd_marginal⟩
  have hcoup : IsCoupling μ ν πInf :=
    IsCoupling.of_weak_limit hπcoup' hπlim hμlim hνlim
  -- Step 2: integrability of coordinate projections against πInf.
  have hmeas_sq : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hae_mem : ∀ᵐ p ∂πInf.toMeasure, p ∈ Icc a b ×ˢ Icc a b := by
    rw [ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff hmeas_sq).mpr hInfSupp
  -- Helper: `|x| ≤ max |a| |b|` when `x ∈ Icc a b`.
  have habs_bound : ∀ x ∈ Icc a b, |x| ≤ max |a| |b| :=
    fun _ ⟨hxa, hxb⟩ => abs_le_max_abs_abs hxa hxb
  have hint_fst : Integrable (fun p : ℝ × ℝ => p.1) πInf.toMeasure :=
    Integrable.mono' (integrable_const (max |a| |b|))
      measurable_fst.aestronglyMeasurable
      (by filter_upwards [hae_mem] with p hp
          rw [Real.norm_eq_abs]; exact habs_bound p.1 hp.1)
  have hint_snd : Integrable (fun p : ℝ × ℝ => p.2) πInf.toMeasure :=
    Integrable.mono' (integrable_const (max |a| |b|))
      measurable_snd.aestronglyMeasurable
      (by filter_upwards [hae_mem] with p hp
          rw [Real.norm_eq_abs]; exact habs_bound p.2 hp.2)
  -- Step 3: tested martingale property for continuous φ, via weak limit.
  have hπmart : ∀ n, ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂(π_seq n).toMeasure = 0 := fun n φ hφm hφb =>
    (hπcoup n).martingale φ hφm hφb
  have hcts : ∀ φ : ℝ → ℝ, Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂πInf.toMeasure = 0 := fun φ hφ_cont hφ_bdd =>
    tested_martingale_of_weak_limit hπsupp hInfSupp hπmart hπlim φ hφ_cont hφ_bdd
  -- Step 4: lift from continuous to measurable.
  have hmart : ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂πInf.toMeasure = 0 :=
    tested_martingale_measurable_of_continuous hInfSupp hint_fst hint_snd hcts
  -- Assemble.
  exact {
    fst_marginal := hcoup.fst_marginal
    snd_marginal := hcoup.snd_marginal
    integrable_fst := hint_fst
    integrable_snd := hint_snd
    martingale := hmart
  }

end Econlib.Probability
