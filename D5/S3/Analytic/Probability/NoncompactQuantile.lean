/- GID: D5/S3/Analytic/Probability/NoncompactQuantile
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/NoncompactQuantile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrable quantile-bin means preserve order and have uniform absolute tails. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
The quantile-bin arguments extend the existing port from danlyng/Econlib
revision d7bd9477476cade1c6695c8891746048ceddc52f to integrable laws.
-/
import D5.S3.Analytic.Probability.ConditionalMeanIntegrable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Equal quantile-bin means for arbitrary integrable real probability laws. -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open Econlib.Probability

noncomputable section

namespace Econlib.Probability.NoncompactQuantile

open Econlib.Probability.DiscreteLaw (bin_endpoints volume_real_bin bins_pairwise_disjoint_Ioc)
private lemma integral_finite_law (p : DiscreteLaw) (f : ℝ → ℝ) :
    ∫ x, f x ∂p.toProbDist.toMeasure = ∑ k, p.weight k * f (p.atom k) := by
  rw [DiscreteLaw.toProbDist_toMeasure,
    integral_finsetSum_measure (fun i _ =>
      (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (p.weight_nonneg _)]

private lemma bin_tail_le {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) {n : ℕ} (hn : 0 < n)
    (k : Fin n) {R : ℝ} (hR : 0 ≤ R) :
    (1 / (n : ℝ)) * (if R < |DiscreteLaw.condMeanAtom μ n hn k|
      then |DiscreteLaw.condMeanAtom μ n hn k| else 0) ≤
      2 * ∫ u in Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        {u : ℝ | R / 2 < |Measure.quantile μ.toMeasure u|}.indicator
          (fun u => |Measure.quantile μ.toMeasure u|) u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hint := DiscreteLaw.integrableOn_quantile_bin_of_integrable hμ hn k
  let q := Measure.quantile μ.toMeasure
  let s := Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n)
  let T := {u : ℝ | R / 2 < |q u|}.indicator (fun u => |q u|)
  have hT : IntegrableOn T s := hint.abs.indicator₀ (by
    simpa only [Real.norm_eq_abs] using
      aestronglyMeasurable_const.nullMeasurableSet_lt hint.aestronglyMeasurable.norm)
  have hTnonneg : 0 ≤ ∫ u in s, T u := integral_nonneg fun _ =>
    indicator_nonneg (fun u _ => abs_nonneg (q u)) _
  by_cases ha : R < |DiscreteLaw.condMeanAtom μ n hn k|
  · rw [ite_eq_left ha]
    have hconst : IntegrableOn (fun _ : ℝ => R / 2) s :=
      integrableOn_const (by dsimp [s]; rw [Real.volume_Ioc]; finiteness)
    have hsplit : (∫ u in s, |q u|) ≤ (1 / (n : ℝ)) * (R / 2) + ∫ u in s, T u := by
      calc
        _ ≤ ∫ u in s, R / 2 + T u := by
          apply integral_mono_ae hint.abs (hconst.add hT)
          filter_upwards with u
          change |q u| ≤ R / 2 + T u
          by_cases hu : R / 2 < |q u|
          · simp only [T, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hu]; linarith
          · simp only [T, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hu, add_zero]; exact le_of_not_gt hu
        _ = _ := by rw [integral_add hconst hT, setIntegral_const, show volume.real s = 1 / (n : ℝ) from volume_real_bin hn k,
          smul_eq_mul]
    have habs : (1 / (n : ℝ)) * |DiscreteLaw.condMeanAtom μ n hn k| ≤ ∫ u in s, |q u| := by
      rw [DiscreteLaw.condMeanAtom, abs_mul, abs_of_pos hnR]
      have hc : (1 / (n : ℝ)) * ((n : ℝ) * |∫ u in s, q u|) = |∫ u in s, q u| := by
        field_simp
      rw [hc]
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (f := q) (μ := volume.restrict s))
    have hpos : 0 < 1 / (n : ℝ) := by positivity
    have hlarge := mul_lt_mul_of_pos_left ha hpos
    dsimp [T, s, q] at *
    linarith
  · rw [ite_eq_right ha, mul_zero]
    exact mul_nonneg (by norm_num) hTnonneg

/-- Conditional means on equal quantile bins have genuine absolute first-moment tails,
uniformly controlled by the original law. -/
theorem absolute_tail_le {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) (n : ℕ) (hn : 0 < n)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in {x : ℝ | R < |x|}, |x|
      ∂(DiscreteLaw.condMeanAtomize μ n hn).toProbDist.toMeasure) ≤
      2 * ∫ x in {x : ℝ | R / 2 < |x|}, |x| ∂μ.toMeasure := by
  let f : ℝ → ℝ := {x : ℝ | R / 2 < |x|}.indicator (fun x => |x|)
  have hf : Integrable f μ.toMeasure := hμ.abs.indicator (measurableSet_lt measurable_const
    continuous_abs.measurable)
  have hq : IntegrableOn (fun u => f (Measure.quantile μ.toMeasure u)) (Ioo (0 : ℝ) 1) := by
    have hh := integrable_map_measure (by
      rw [Measure.map_quantile_volume_Ioo]; exact hf.aestronglyMeasurable)
      (Measure.aemeasurable_quantile_restrict_Ioo (μ := μ.toMeasure))
    rw [Measure.map_quantile_volume_Ioo] at hh
    exact hh.mp hf
  rw [← integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable),
    integral_finite_law]
  change (∑ k : Fin n, (1 / (n : ℝ)) *
    {x : ℝ | R < |x|}.indicator (fun x => |x|) (DiscreteLaw.condMeanAtom μ n hn k)) ≤ _
  calc
    _ ≤ ∑ k : Fin n, 2 * ∫ u in Ioc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        f (Measure.quantile μ.toMeasure u) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [f, Set.indicator_apply, Set.mem_ofPred_eq] using bin_tail_le hμ hn k hR
    _ = 2 * ∫ u in Ioo (0 : ℝ) 1, f (Measure.quantile μ.toMeasure u) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [← integral_Ico_eq_integral_Ioc]
      rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico)
        (Measure.bins_pairwise_disjoint n)]
      · rw [Measure.iUnion_bins_eq_Ico n hn, integral_Ico_eq_integral_Ioo]
      · intro k
        rw [integrableOn_Ico_iff_integrableOn_Ioo]
        exact hq.mono_set fun u hu =>
          ⟨lt_of_le_of_lt (bin_endpoints hn k).1 hu.1,
            lt_of_lt_of_le hu.2 (bin_endpoints hn k).2.1⟩
    _ = _ := by
      rw [← Measure.integral_eq_integral_quantile f hf.aestronglyMeasurable]
      dsimp only [f]
      rw [integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)]

open DiscreteLaw

private theorem means_order {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id)
    (hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z) (n : ℕ) (hn : 0 < n) :
    DiscreteLaw.ConvexOrder
      (DiscreteLaw.condMeanAtomize μ n hn)
      (DiscreteLaw.condMeanAtomize ν n hn) :=
  condMeanAtomize_convexOrder_of_lowerIntegratedQuantile hμ hν hmean n hn fun ht =>
    lowerIntegratedQuantile_ge_of_upper_le hμ hν hmean ht
      (upperIntegratedQuantile_le_of_stopLoss_le hμ hν hstop ht)

private lemma uniform_absolute_tails {μ : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ n : ℕ,
      (∫ x in {x : ℝ | R < |x|}, |x|
        ∂(condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure) < ε := by
  have htend : Tendsto (fun m : ℕ => ∫ x,
      {x : ℝ | (m : ℝ) < |x|}.indicator (fun x => |x|) x ∂μ.toMeasure)
      atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence
      (F := fun m : ℕ => {x : ℝ | (m : ℝ) < |x|}.indicator (fun x => |x|))
      (f := fun _ : ℝ => (0 : ℝ)) (bound := fun x : ℝ => |x|)
      (fun m => (hμ.abs.indicator (measurableSet_lt measurable_const
        continuous_abs.measurable)).aestronglyMeasurable) hμ.abs
      (fun m => ae_of_all _ fun x => by
        by_cases hx : (m : ℝ) < |x| <;>
          simp [Set.indicator_apply, hx, Real.norm_eq_abs, abs_nonneg])
      (ae_of_all _ fun x => ?_)
    · simpa using hh
    · obtain ⟨N, hN⟩ := exists_nat_gt |x|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with m hm
      have hx : ¬(m : ℝ) < |x| := by
        have : (N : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      simp [hx]
  intro ε hε
  have hsmall := htend.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨2 * ((N + 1 : ℕ) : ℝ), by positivity, fun n => ?_⟩
  have hb := absolute_tail_le hμ (n + 1) (Nat.succ_pos n)
    (R := 2 * ((N + 1 : ℕ) : ℝ)) (by positivity)
  have he := hN (N + 1) (by omega)
  rw [integral_indicator (measurableSet_lt measurable_const continuous_abs.measurable)] at he
  have hr : 2 * ((N + 1 : ℕ) : ℝ) / 2 = ((N + 1 : ℕ) : ℝ) := by ring
  rw [hr] at hb
  linarith

private lemma tail_map (ρ : Measure (ℝ × ℝ)) (g : ℝ × ℝ → ℝ)
    (hg : Measurable g) (R : ℝ) :
    (∫ p in {p : ℝ × ℝ | R < |g p|}, |g p| ∂ρ) =
      ∫ x in {x : ℝ | R < |x|}, |x| ∂Measure.map g ρ := by
  let f : ℝ → ℝ := {x : ℝ | R < |x|}.indicator (fun x => |x|)
  have hf : Measurable f := continuous_abs.measurable.indicator
    (measurableSet_lt measurable_const continuous_abs.measurable)
  rw [← integral_indicator (s := {p : ℝ × ℝ | R < |g p|})
      (f := fun p => |g p|) (measurableSet_lt measurable_const
        (continuous_abs.measurable.comp hg)),
    ← integral_indicator (s := {x : ℝ | R < |x|}) (f := fun x => |x|)
      (measurableSet_lt measurable_const continuous_abs.measurable)]
  exact (integral_map hg.aemeasurable hf.aestronglyMeasurable).symm

/-- Equal-resolution quantile-bin laws admit actual finite martingale joints,
converge to the original integrable marginals, and have uniform joint coordinate tails. -/
theorem exists_martingale_approximations {μ ν : ProbDist ℝ}
    (hμ : Integrable (fun x : ℝ => x) μ.toMeasure)
    (hν : Integrable (fun x : ℝ => x) ν.toMeasure)
    (hmean : μ.expect id = ν.expect id)
    (hstop : ∀ z : ℝ, μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z) :
    ∃ π : ℕ → ProbDist (ℝ × ℝ),
      (∀ n, IsMartingaleCoupling
        (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
        (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist (π n)) ∧
      Tendsto (fun n => (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist)
        atTop (𝓝 μ) ∧
      Tendsto (fun n => (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist)
        atTop (𝓝 ν) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ n,
        (∫ p in {p : ℝ × ℝ | R < |p.1|}, |p.1| ∂(π n).toMeasure) +
        (∫ p in {p : ℝ × ℝ | R < |p.2|}, |p.2| ∂(π n).toMeasure) < ε) := by
  have hex : ∀ n : ℕ, ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling
      (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist
      (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist π := by
    intro n
    exact DiscreteLaw.exists_martingaleCoupling_uniform _ _ (Nat.succ_pos n) rfl
      (fun _ => rfl) (fun _ => rfl) (means_order hμ hν hmean hstop _ (Nat.succ_pos n))
  choose π hπ using hex
  refine ⟨π, hπ,
    DiscreteLaw.condMeanAtomize_tendsto_of_integrable_bins
      (fun _ hn k => DiscreteLaw.integrableOn_quantile_bin_of_integrable hμ hn k),
    DiscreteLaw.condMeanAtomize_tendsto_of_integrable_bins
      (fun _ hn k => DiscreteLaw.integrableOn_quantile_bin_of_integrable hν hn k), ?_⟩
  intro ε hε
  obtain ⟨Rμ, hRμ, hbμ⟩ := uniform_absolute_tails hμ (ε / 2) (by linarith)
  obtain ⟨Rν, hRν, hbν⟩ := uniform_absolute_tails hν (ε / 2) (by linarith)
  refine ⟨max Rμ Rν, lt_max_of_lt_left hRμ, fun n => ?_⟩
  rw [tail_map _ _ measurable_fst, tail_map _ _ measurable_snd]
  change (∫ x in {x : ℝ | max Rμ Rν < |x|}, |x|
    ∂(π n).toMeasure.fst) + (∫ x in {x : ℝ | max Rμ Rν < |x|}, |x|
    ∂(π n).toMeasure.snd) < ε
  rw [(hπ n).fst_measure, (hπ n).snd_measure]
  have hsubμ : {x : ℝ | max Rμ Rν < |x|} ⊆ {x : ℝ | Rμ < |x|} :=
    fun x hx => show Rμ < |x| from lt_of_le_of_lt (le_max_left Rμ Rν) hx
  have hsubν : {x : ℝ | max Rμ Rν < |x|} ⊆ {x : ℝ | Rν < |x|} :=
    fun x hx => show Rν < |x| from lt_of_le_of_lt (le_max_right Rμ Rν) hx
  have hμint : Integrable (fun x : ℝ => |x|)
      (condMeanAtomize μ (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure := by
    rw [DiscreteLaw.toProbDist_toMeasure]
    exact integrable_finsetSum_measure.mpr fun i _ =>
      (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hνint : Integrable (fun x : ℝ => |x|)
      (condMeanAtomize ν (n + 1) (Nat.succ_pos n)).toProbDist.toMeasure := by
    rw [DiscreteLaw.toProbDist_toMeasure]
    exact integrable_finsetSum_measure.mpr fun i _ =>
      (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hu := setIntegral_mono_set hμint.integrableOn (ae_of_all _ fun x => abs_nonneg x)
    (ae_of_all _ hsubμ)
  have hv := setIntegral_mono_set hνint.integrableOn (ae_of_all _ fun x => abs_nonneg x)
    (ae_of_all _ hsubν)
  refine (add_le_add hu hv).trans_lt ?_
  have htail := add_lt_add (hbμ n) (hbν n)
  rwa [add_halves] at htail

/-- Continuous bounded displacement tests determine all measurable bounded displacement tests
when both coordinates are integrable. -/
theorem tested_measurable_of_continuous {π : ProbDist (ℝ × ℝ)}
    (hint_fst : Integrable (fun p : ℝ × ℝ => p.1) π.toMeasure)
    (hint_snd : Integrable (fun p : ℝ × ℝ => p.2) π.toMeasure)
    (hcts : ∀ φ : ℝ → ℝ, Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0) :
    ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0 := by
  have h_diff_int : Integrable (fun p : ℝ × ℝ => p.2 - p.1) π.toMeasure :=
    hint_snd.sub hint_fst
  have h_abs_int : Integrable (fun p : ℝ × ℝ => |p.2 - p.1|) π.toMeasure := h_diff_int.abs
  let posW : ℝ × ℝ → NNReal := fun p => Real.toNNReal (p.2 - p.1)
  let negW : ℝ × ℝ → NNReal := fun p => Real.toNNReal (-(p.2 - p.1))
  have hposW_meas : Measurable posW :=
    (measurable_snd.sub measurable_fst).real_toNNReal
  have hnegW_meas : Measurable negW :=
    ((measurable_snd.sub measurable_fst).neg).real_toNNReal
  have h_pos_coe : ∀ p : ℝ × ℝ, ((posW p : ℝ)) = max (p.2 - p.1) 0 := by
    intro p; exact Real.coe_toNNReal' _
  have h_neg_coe : ∀ p : ℝ × ℝ, ((negW p : ℝ)) = max (-(p.2 - p.1)) 0 := by
    intro p; exact Real.coe_toNNReal' _
  have h_decomp : ∀ p : ℝ × ℝ, (posW p : ℝ) - (negW p : ℝ) = p.2 - p.1 := by
    intro p; rw [h_pos_coe, h_neg_coe]; exact max_zero_sub_eq_self _
  have h_pos_le_abs : ∀ p : ℝ × ℝ, (posW p : ℝ) ≤ |p.2 - p.1| := by
    intro p; rw [h_pos_coe]; exact max_le (le_abs_self _) (abs_nonneg _)
  have h_neg_le_abs : ∀ p : ℝ × ℝ, (negW p : ℝ) ≤ |p.2 - p.1| := by
    intro p; rw [h_neg_coe]; exact max_le (neg_le_abs _) (abs_nonneg _)
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
  let posE : ℝ × ℝ → ENNReal := fun p => (posW p : ENNReal)
  let negE : ℝ × ℝ → ENNReal := fun p => (negW p : ENNReal)
  have hposE_meas : Measurable posE := hposW_meas.coe_nnreal_ennreal
  have hnegE_meas : Measurable negE := hnegW_meas.coe_nnreal_ennreal
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
  haveI h_pos_fin : IsFiniteMeasure (π.toMeasure.withDensity posE) :=
    isFiniteMeasure_withDensity hposE_lint_ne
  haveI h_neg_fin : IsFiniteMeasure (π.toMeasure.withDensity negE) :=
    isFiniteMeasure_withDensity hnegE_lint_ne
  let μ_pos : MeasureTheory.Measure ℝ := (π.toMeasure.withDensity posE).map Prod.fst
  let μ_neg : MeasureTheory.Measure ℝ := (π.toMeasure.withDensity negE).map Prod.fst
  haveI : IsFiniteMeasure μ_pos := Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure μ_neg := Measure.isFiniteMeasure_map _ _
  have int_pos : ∀ (g : ℝ → ℝ) (_ : AEStronglyMeasurable g μ_pos),
      ∫ x, g x ∂μ_pos = ∫ p, (posW p : ℝ) * g (p.1) ∂π.toMeasure := by
    intro g hg
    change ∫ x, g x ∂((π.toMeasure.withDensity posE).map Prod.fst) = _
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable hg]
    rw [integral_withDensity_eq_integral_smul hposW_meas]
    simp only [smul_eq_mul, NNReal.smul_def]
  have int_neg : ∀ (g : ℝ → ℝ) (_ : AEStronglyMeasurable g μ_neg),
      ∫ x, g x ∂μ_neg = ∫ p, (negW p : ℝ) * g (p.1) ∂π.toMeasure := by
    intro g hg
    change ∫ x, g x ∂((π.toMeasure.withDensity negE).map Prod.fst) = _
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable hg]
    rw [integral_withDensity_eq_integral_smul hnegW_meas]
    simp only [smul_eq_mul, NNReal.smul_def]
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
    have h_sub := h_sub_gen (f : ℝ → ℝ) hf_meas hf_bdd
    have h_ct := hcts (f : ℝ → ℝ) hf_cts hf_bdd
    linarith
  intro φ hφ_meas hφ_bdd
  obtain ⟨M, hM⟩ := hφ_bdd
  have hφ_aesm_pos : AEStronglyMeasurable φ μ_pos := hφ_meas.aestronglyMeasurable
  have hφ_aesm_neg : AEStronglyMeasurable φ μ_neg := hφ_meas.aestronglyMeasurable
  have heq : ∫ x, φ x ∂μ_pos = ∫ x, φ x ∂μ_neg := by rw [hμ_eq]
  rw [int_pos φ hφ_aesm_pos, int_neg φ hφ_aesm_neg] at heq
  have h_sub := h_sub_gen φ hφ_meas ⟨M, hM⟩
  linarith
end Econlib.Probability.NoncompactQuantile
