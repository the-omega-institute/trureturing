/- GID: D5/S3/Analytic/Probability/SkorokhodRepresentation
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/SkorokhodRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full native Polish-space Skorokhod representation on a fixed unit interval. -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import D5.S3.Analytic.Probability.CompactQuantile
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.UniformSpace.Uniformizable

section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal

namespace D5.S3.Analytic.Probability.SkorokhodRepresentation

/-!
# Skorokhod representation theorem

Weak convergence of Borel probability measures on a Polish space admits
a full-sequence almost-sure realization on the fixed unit interval.

Adapted from facebookresearch/atlas-lean, revision
`a60759060b5616df0d5775b42da4d337719feb32`,
`MathlibExt/Probability/SkorokhodRepresentation.lean`. The source license, including
its intended-use preface, is retained at `docs/reports/lovasz-suppliers/atlas-LICENSE.txt`.
-/

private theorem exists_null_singleton_mem_Ioo {ν : Measure ℝ} [SFinite ν]
    {a b : ℝ} (hab : a < b) : ∃ t, a < t ∧ t < b ∧ ν {t} = 0 := by
  have hset : ∀ t : ℝ, ({t} : Set ℝ) = {a : ℝ | (id : ℝ → ℝ) a = t} := by
    intro t
    ext s
    simp
  have hcount : {t : ℝ | 0 < ν {a : ℝ | (id : ℝ → ℝ) a = t}}.Countable :=
    Measure.countable_meas_level_set_pos measurable_id
  have hcount2 : {t : ℝ | 0 < ν {t}}.Countable := by
    simp only [hset]
    exact hcount
  have hdense : Dense ({t : ℝ | 0 < ν {t}}ᶜ) :=
    Set.Countable.dense_compl ℝ hcount2
  obtain ⟨t, htmem, hat, htb⟩ := Dense.exists_between hdense hab
  refine ⟨t, hat, htb, ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at htmem
  exact nonpos_iff_eq_zero.mp htmem

private theorem quantile_le_iff_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {u x : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    quantile ν u ≤ x ↔ u ≤ ProbabilityTheory.cdf ν x := by
  rw [quantile_le_iff hu, ProbabilityTheory.cdf_eq_real]
  rfl

private theorem tendsto_quantile_of_continuousAt
    (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ν₀]
    (hconv : ∀ t : ℝ, ν₀ {t} = 0 →
      Filter.Tendsto (fun n => ProbabilityTheory.cdf (ν n) t) Filter.atTop
        (nhds (ProbabilityTheory.cdf ν₀ t)))
    {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) 1) (hcont : ContinuousAt (quantile ν₀) u) :
    Filter.Tendsto (fun n => quantile (ν n) u) Filter.atTop
      (nhds (quantile ν₀ u)) := by
  have hu0 : (0:ℝ) < u := hu.1
  have hu1 : u < 1 := hu.2
  rw [tendsto_order]
  constructor
  · -- lower half: no continuity needed
    intro a ha
    obtain ⟨t, hat, htQ, htnull⟩ := exists_null_singleton_mem_Ioo (ν := ν₀) ha
    have hFlt : ProbabilityTheory.cdf ν₀ t < u := by
      have h : ¬ (u ≤ ProbabilityTheory.cdf ν₀ t) :=
        (Iff.not (quantile_le_iff_cdf ν₀ (x := t) hu)).mp (not_le_of_gt htQ)
      exact lt_of_not_ge h
    have hev : ∀ᶠ n in Filter.atTop, ProbabilityTheory.cdf (ν n) t < u :=
      Filter.Tendsto.eventually_lt_const hFlt (hconv t htnull)
    filter_upwards [hev] with n hn
    have htnQ : t < quantile (ν n) u := by
      apply lt_of_not_ge
      intro hle
      have hle2 : u ≤ ProbabilityTheory.cdf (ν n) t :=
        (quantile_le_iff_cdf (ν n) hu).mp hle
      exact absurd hle2 (not_le_of_gt hn)
    exact lt_trans hat htnQ
  · -- upper half
    intro b hb
    have hevQ : ∀ᶠ v in nhds u, quantile ν₀ v < b ∧ v < 1 := by
      apply Filter.Eventually.and
      · exact hcont.eventually_lt continuousAt_const hb
      · exact Iio_mem_nhds hu1
    obtain ⟨v, huv, hvb, hv1⟩ := Filter.Eventually.exists_gt hevQ
    have hv0 : 0 < v := lt_trans hu0 huv
    have hvIoo : v ∈ Set.Ioo (0:ℝ) 1 := ⟨hv0, hv1⟩
    obtain ⟨t, hvt, htb, htnull⟩ := exists_null_singleton_mem_Ioo (ν := ν₀) hvb
    have hvF : v ≤ ProbabilityTheory.cdf ν₀ t :=
      (quantile_le_iff_cdf ν₀ hvIoo).mp (le_of_lt hvt)
    have huF : u < ProbabilityTheory.cdf ν₀ t := lt_of_lt_of_le huv hvF
    have hev : ∀ᶠ n in Filter.atTop, u < ProbabilityTheory.cdf (ν n) t :=
      Filter.Tendsto.eventually_const_lt huF (hconv t htnull)
    filter_upwards [hev] with n hn
    have hnQ : quantile (ν n) u ≤ t :=
      (quantile_le_iff_cdf (ν n) hu).mpr (le_of_lt hn)
    exact lt_of_le_of_lt hnQ htb

private theorem ae_tendsto_quantile
    (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ)
    [∀ n, IsProbabilityMeasure (ν n)] [IsProbabilityMeasure ν₀]
    (hconv : ∀ t : ℝ, ν₀ {t} = 0 →
      Filter.Tendsto (fun n => ProbabilityTheory.cdf (ν n) t) Filter.atTop
        (nhds (ProbabilityTheory.cdf ν₀ t))) :
    ∀ᵐ u ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      Filter.Tendsto (fun n => quantile (ν n) u) Filter.atTop
        (nhds (quantile ν₀ u)) := by
  set Bad : Set ℝ :=
    {u | u ∈ Set.Ioo (0:ℝ) 1 ∧ ¬ContinuousWithinAt (quantile ν₀) (Set.Ioo (0:ℝ) 1) u}
  have hBad_count : Bad.Countable :=
    countable_not_continuousWithinAt_quantile
  have hBad_null : volume Bad = 0 := hBad_count.measure_zero volume
  have h01_null : volume ({0} ∪ {1} : Set ℝ) = 0 :=
    measure_union_null Real.volume_singleton Real.volume_singleton
  have hae_vol : ∀ᵐ u ∂volume, u ∉ Bad ∧ u ∉ ({0} ∪ {1} : Set ℝ) := by
    rw [ae_iff]
    have hset : {u : ℝ | ¬(u ∉ Bad ∧ u ∉ ({0} ∪ {1} : Set ℝ))} =
        Bad ∪ ({0} ∪ {1} : Set ℝ) := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      tauto
    rw [hset]
    exact measure_union_null hBad_null h01_null
  have hae : ∀ᵐ u ∂(volume.restrict (Set.Icc (0:ℝ) 1)),
      (u ∉ Bad ∧ u ∉ ({0} ∪ {1} : Set ℝ)) ∧ u ∈ Set.Icc (0:ℝ) 1 :=
    (ae_restrict_of_ae hae_vol).and (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hae] with u hu
  obtain ⟨⟨hBad, h01⟩, hIcc⟩ := hu
  have hne0 : u ≠ 0 := fun h => h01 (Or.inl (Set.mem_singleton_iff.mpr h))
  have hne1 : u ≠ 1 := fun h => h01 (Or.inr (Set.mem_singleton_iff.mpr h))
  have hu0' : (0:ℝ) ≤ u := hIcc.1
  have hu1' : u ≤ 1 := hIcc.2
  have hu0 : (0:ℝ) < u := lt_of_le_of_ne hu0' (Ne.symm hne0)
  have hu1 : u < 1 := lt_of_le_of_ne hu1' hne1
  have huIoo : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu0, hu1⟩
  have hwithin : ContinuousWithinAt (quantile ν₀) (Set.Ioo (0:ℝ) 1) u := by
    by_contra hcon
    exact hBad ⟨huIoo, hcon⟩
  have hcont : ContinuousAt (quantile ν₀) u :=
    hwithin.continuousAt (Ioo_mem_nhds hu0 hu1)
  exact tendsto_quantile_of_continuousAt ν ν₀ hconv huIoo hcont

private theorem frontier_preimage_subset_discont {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (E : Set Y) :
    frontier (f ⁻¹' E) ⊆ {x | ¬ ContinuousAt f x} ∪ f ⁻¹' (frontier E) := by
  intro x hx
  by_cases hcont : ContinuousAt f x
  · right
    rw [frontier_eq_closure_inter_closure] at hx ⊢
    simp only [Set.mem_inter_iff] at hx
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    have him1 : f x ∈ closure (f '' (f ⁻¹' E)) :=
      hcont.continuousWithinAt.mem_closure_image hx.1
    have hx2 : x ∈ closure (f ⁻¹' Eᶜ) := by
      have hcompl : (f ⁻¹' E)ᶜ = f ⁻¹' Eᶜ := by rw [Set.preimage_compl]
      have h2 := hx.2
      rwa [hcompl] at h2
    have him2 : f x ∈ closure (f '' (f ⁻¹' Eᶜ)) :=
      hcont.continuousWithinAt.mem_closure_image hx2
    exact ⟨closure_mono (Set.image_preimage_subset f E) him1,
           closure_mono (Set.image_preimage_subset f Eᶜ) him2⟩
  · left
    exact hcont

private theorem tendsto_cdf_map_of_null_atom
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X]
    (μ : ℕ → ProbabilityMeasure X) (μ₀ : ProbabilityMeasure X)
    (hμ : Filter.Tendsto (fun n => μ n) Filter.atTop (nhds μ₀))
    (Φ : X → ℝ) (hΦ : Measurable Φ)
    (hnull : (↑μ₀ : Measure X) {x | ¬ ContinuousAt Φ x} = 0)
    (t : ℝ) (ht : (Measure.map Φ (↑μ₀ : Measure X)) {t} = 0) :
    Filter.Tendsto
      (fun n => ProbabilityTheory.cdf (Measure.map Φ (↑(μ n) : Measure X)) t)
      Filter.atTop
      (nhds (ProbabilityTheory.cdf (Measure.map Φ (↑μ₀ : Measure X)) t)) := by
  set E : Set X := Φ ⁻¹' (Set.Iic t) with hE
  have hfront_sub : frontier E ⊆ {x | ¬ ContinuousAt Φ x} ∪ Φ ⁻¹' {t} := by
    have h := frontier_preimage_subset_discont Φ (Set.Iic t)
    rwa [frontier_Iic] at h
  have hpre_single : (↑μ₀ : Measure X) (Φ ⁻¹' {t}) = 0 := by
    have hmap : (Measure.map Φ (↑μ₀ : Measure X)) {t} = (↑μ₀ : Measure X) (Φ ⁻¹' {t}) :=
      Measure.map_apply hΦ (measurableSet_singleton t)
    rw [← hmap]
    exact ht
  have hU : (↑μ₀ : Measure X) ({x | ¬ ContinuousAt Φ x} ∪ Φ ⁻¹' {t}) = 0 :=
    measure_union_null hnull hpre_single
  have hF : (↑μ₀ : Measure X) (frontier E) = 0 :=
    measure_mono_null hfront_sub hU
  have hFnn : μ₀ (frontier E) = 0 := by
    have hcoe := ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure μ₀ (frontier E)
    rw [hF] at hcoe
    exact ENNReal.coe_eq_zero.mp hcoe
  have hportE : Filter.Tendsto (fun n => (μ n) E) Filter.atTop (nhds (μ₀ E)) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hμ hFnn
  -- push to ℝ
  have hreal : Filter.Tendsto (fun n => ((μ n) E : ℝ)) Filter.atTop
      (nhds ((μ₀ E : ℝ))) :=
    NNReal.tendsto_coe.mpr hportE
  -- identify with cdf
  have hid : ∀ ν : ProbabilityMeasure X,
      ((ν E : ℝ)) = ProbabilityTheory.cdf (Measure.map Φ (↑ν : Measure X)) t := by
    intro ν
    have hmap : (Measure.map Φ (↑ν : Measure X)) (Set.Iic t) = (↑ν : Measure X) E :=
      Measure.map_apply hΦ measurableSet_Iic
    have hcdf : (ProbabilityTheory.cdf (Measure.map Φ (↑ν : Measure X)) t : ℝ) =
        (Measure.map Φ (↑ν : Measure X)).real (Set.Iic t) :=
      ProbabilityTheory.cdf_eq_real _ t
    rw [hcdf, Measure.real_def]
    -- goal: ↑(ν E) = ((map ...) (Iic t)).toReal ; rewrite map
    rw [hmap]
    have hcoe : (ν : ProbabilityMeasure X) E = ((↑ν : Measure X) E).toNNReal := by
      rw [ProbabilityMeasure.coeFn_def]
    rw [hcoe]
    exact (ENNReal.coe_toNNReal_eq_toReal _).symm
  simp_rw [hid] at hreal
  exact hreal

private theorem exists_null_frontier_ball_cover
    {X : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X] [Nonempty X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (ρ : Measure X) [SFinite ρ] :
    ∃ (c : ℕ → X) (r : ℕ → ℝ),
      (∀ m, 0 < r m) ∧
      (∀ m, ρ (frontier (Metric.ball (c m) (r m))) = 0) ∧
      (∀ (x : X) (ε : ℝ), 0 < ε → ∃ m, x ∈ Metric.ball (c m) (r m) ∧ r m < ε) := by
  have hpow : ∀ k : ℕ, (1/2 : ℝ)^(k+1) < (1/2)^k := by
    intro k
    have h : (1/2 : ℝ)^(k+1) = (1/2)^k * (1/2) := pow_succ (1/2) k
    rw [h]
    have hpos : (0:ℝ) < (1/2)^k := pow_pos (by norm_num) k
    have hlt := mul_lt_mul_of_pos_left (show (1/2:ℝ) < 1 by norm_num) hpos
    simpa using hlt
  have hex : ∀ i k : ℕ, ∃ R ∈ Set.Ioo ((1/2:ℝ)^(k+1)) ((1/2:ℝ)^k),
      ρ (frontier (Metric.thickening R {TopologicalSpace.denseSeq X i})) = 0 :=
    fun i k => exists_null_frontier_thickening ρ _ (hpow k)
  choose R hRmem hRnull using hex
  refine ⟨fun m => TopologicalSpace.denseSeq X (Nat.unpair m).1,
    fun m => R (Nat.unpair m).1 (Nat.unpair m).2, ?_, ?_, ?_⟩
  · intro m
    have h := (hRmem (Nat.unpair m).1 (Nat.unpair m).2).1
    have h2 : (0:ℝ) ≤ (1/2)^((Nat.unpair m).2 + 1) :=
      le_of_lt (pow_pos (by norm_num) _)
    exact lt_of_le_of_lt h2 h
  · intro m
    have hball : Metric.ball (TopologicalSpace.denseSeq X (Nat.unpair m).1)
        (R (Nat.unpair m).1 (Nat.unpair m).2) =
        Metric.thickening (R (Nat.unpair m).1 (Nat.unpair m).2)
          {TopologicalSpace.denseSeq X (Nat.unpair m).1} := by
      rw [Metric.thickening_singleton]
    rw [hball]
    exact hRnull (Nat.unpair m).1 (Nat.unpair m).2
  · intro x ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (show (1/2:ℝ) < 1 by norm_num)
    have hpos2 : (0:ℝ) < (1/2)^(k+1) := pow_pos (by norm_num) _
    obtain ⟨i, hi⟩ := (TopologicalSpace.denseRange_denseSeq X).exists_dist_lt x hpos2
    refine ⟨Nat.pair i k, ?_, ?_⟩
    · simp only [Nat.unpair_pair]
      rw [Metric.mem_ball]
      have hRlo := (hRmem i k).1
      exact lt_trans hi hRlo
    · simp only [Nat.unpair_pair]
      have hRhi := (hRmem i k).2
      exact lt_trans hRhi hk

open Classical in
private theorem tendsto_of_tendsto_ballAddress
    {X : Type*} [PseudoMetricSpace X]
    (c : ℕ → X) (r : ℕ → ℝ)
    (hcover : ∀ (x : X) (ε : ℝ), 0 < ε → ∃ m, x ∈ Metric.ball (c m) (r m) ∧ r m < ε)
    {ι : Type*} {l : Filter ι} {y : ι → X} {x : X}
    (h : Filter.Tendsto (fun i m => decide (y i ∈ Metric.ball (c m) (r m))) l
      (nhds (fun m => decide (x ∈ Metric.ball (c m) (r m))))) :
    Filter.Tendsto y l (nhds x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hmem, hrm⟩ := hcover x (ε / 2) (by linarith)
  have hcoord : Filter.Tendsto (fun i => decide (y i ∈ Metric.ball (c m) (r m))) l
      (nhds (decide (x ∈ Metric.ball (c m) (r m)))) :=
    (tendsto_pi_nhds.mp h) m
  rw [nhds_discrete] at hcoord
  have hev : ∀ᶠ i in l, decide (y i ∈ Metric.ball (c m) (r m)) =
      decide (x ∈ Metric.ball (c m) (r m)) := Filter.tendsto_pure.mp hcoord
  have htrue : decide (x ∈ Metric.ball (c m) (r m)) = true :=
    decide_eq_true_iff.mpr hmem
  filter_upwards [hev] with i hi
  have hyi : y i ∈ Metric.ball (c m) (r m) := by
    have : decide (y i ∈ Metric.ball (c m) (r m)) = true := by
      rw [hi, htrue]
    exact decide_eq_true_iff.mp this
  rw [Metric.mem_ball] at hmem hyi
  -- dist (y i) x ≤ dist (y i) (c m) + dist (c m) x < rm + rm < ε
  have h1 : dist (y i) x ≤ dist (y i) (c m) + dist (c m) x := dist_triangle _ _ _
  have h2 : dist (c m) x = dist x (c m) := dist_comm _ _
  rw [h2] at h1
  linarith

open Classical in
private theorem continuousAt_ballAddress
    {X : Type*} [PseudoMetricSpace X]
    (c : ℕ → X) (r : ℕ → ℝ)
    {x : X} (hx : ∀ m, x ∉ frontier (Metric.ball (c m) (r m))) :
    ContinuousAt (fun x' m => decide (x' ∈ Metric.ball (c m) (r m))) x := by
  rw [continuousAt_pi]
  intro m
  set B := Metric.ball (c m) (r m) with hB
  by_cases hxmem : x ∈ B
  · have heq : (fun x' : X => decide (x' ∈ B)) =ᶠ[nhds x] (fun _ => true) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxmem] with x' hx'
      exact decide_eq_true_iff.mpr hx'
    exact heq.continuousAt
  · have hxcl : x ∈ closure Bᶜ := subset_closure hxmem
    -- x ∉ frontier B and x ∈ closure Bᶜ forces x ∉ closure B
    have hxnc : x ∉ closure B := by
      intro hmem
      have hfront : x ∈ frontier B := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨hmem, hxcl⟩
      exact hx m hfront
    have heq : (fun x' : X => decide (x' ∈ B)) =ᶠ[nhds x] (fun _ => false) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxnc] with x' hx'
      simp only [Set.mem_compl_iff] at hx'
      have : x' ∉ B := fun hmem => hx' (subset_closure hmem)
      exact decide_eq_false_iff_not.mpr this
    exact heq.continuousAt

private theorem exists_measurableEmbedding_ae_continuous_reflecting
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ₀ : ProbabilityMeasure X) :
    ∃ Φ : X → ℝ, MeasurableEmbedding Φ ∧
      (↑μ₀ : Measure X) {x | ¬ ContinuousAt Φ x} = 0 ∧
      (∀ (y : ℕ → X) (x : X),
        Filter.Tendsto (fun n => Φ (y n)) Filter.atTop (nhds (Φ x)) →
        Filter.Tendsto y Filter.atTop (nhds x)) := by
  classical
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have : Nonempty X := nonempty_of_isProbabilityMeasure (↑μ₀ : Measure X)
  obtain ⟨c, r, hpos, hnull, hcover⟩ :=
    exists_null_frontier_ball_cover (X := X) (ρ := (↑μ₀ : Measure X))
  -- address map and embedding
  set a : X → (ℕ → Bool) := fun x m => decide (x ∈ Metric.ball (c m) (r m)) with ha
  set C : (ℕ → Bool) → ℝ :=
    fun b => (cantorSetHomeomorphNatToBool.symm b : ℝ) with hC
  set Φ : X → ℝ := C ∘ a with hΦ
  have hCantorEmb : Topology.IsEmbedding C :=
    Topology.IsEmbedding.subtypeVal.comp cantorSetHomeomorphNatToBool.symm.isEmbedding
  have hCantorCont : Continuous C := hCantorEmb.continuous
  -- measurability of a
  have ha_meas : Measurable a := by
    rw [measurable_pi_iff]
    intro m
    apply measurable_to_bool
    have hpre : (fun x : X => decide (x ∈ Metric.ball (c m) (r m))) ⁻¹' {true} =
        Metric.ball (c m) (r m) := by
      ext x
      simp
    rw [hpre]
    exact measurableSet_ball
  have hΦ_meas : Measurable Φ := hCantorCont.measurable.comp ha_meas
  -- reflection: C ∘ a reflects via IsEmbedding + N3
  have hreflect : ∀ (y : ℕ → X) (x : X),
      Filter.Tendsto (fun n => Φ (y n)) Filter.atTop (nhds (Φ x)) →
      Filter.Tendsto y Filter.atTop (nhds x) := by
    intro y x h
    have ha_lim : Filter.Tendsto (fun n => a (y n)) Filter.atTop (nhds (a x)) := by
      have h2 : Filter.Tendsto (C ∘ (fun n => a (y n))) Filter.atTop (nhds (C (a x))) := h
      exact hCantorEmb.tendsto_nhds_iff.mpr h2
    exact tendsto_of_tendsto_ballAddress c r hcover ha_lim
  -- injectivity from reflection
  have hinj : Function.Injective Φ := by
    intro x y hxy
    have hlim : Filter.Tendsto (fun _ : ℕ => Φ y) Filter.atTop (nhds (Φ x)) := by
      rw [hxy]
      exact tendsto_const_nhds
    have := hreflect (fun _ => y) x hlim
    rw [tendsto_const_nhds_iff] at this
    exact this.symm
  have hME : MeasurableEmbedding Φ := hΦ_meas.measurableEmbedding hinj
  refine ⟨Φ, hME, ?_, hreflect⟩
  -- discontinuity set null
  have hsub : {x | ¬ ContinuousAt Φ x} ⊆ ⋃ m, frontier (Metric.ball (c m) (r m)) := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hmem
    simp only [Set.mem_iUnion, not_exists] at hmem
    have hacont : ContinuousAt a x := continuousAt_ballAddress c r (fun m => hmem m)
    have : ContinuousAt Φ x := (hCantorCont.continuousAt).comp hacont
    exact hx this
  exact measure_mono_null hsub (measure_iUnion_null (fun m => hnull m))

/-- A weakly convergent sequence of Borel probability laws on an arbitrary Polish
space has globally measurable copies on the same fixed unit-interval Lebesgue space,
with the exact laws and almost-sure convergence of the full sequence. -/
theorem skorokhod_representation
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → ProbabilityMeasure X) (μ₀ : ProbabilityMeasure X)
    (hμ : Filter.Tendsto (fun n => μ n) Filter.atTop (nhds μ₀)) :
    ∃ (Y : ℕ → ℝ → X) (Y₀ : ℝ → X),
      (∀ n, Measurable (Y n)) ∧ Measurable Y₀ ∧
      (∀ n, (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))).map (Y n) = (μ n : Measure X)) ∧
      (volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))).map Y₀ = (μ₀ : Measure X) ∧
      ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) (1 : ℝ))),
        Filter.Tendsto (fun n => Y n x) Filter.atTop (nhds (Y₀ x)) := by
  have : Nonempty X := MeasureTheory.nonempty_of_isProbabilityMeasure (μ₀ : Measure X)
  obtain ⟨Φ, hemb, hdiscont, hrefl⟩ :=
    exists_measurableEmbedding_ae_continuous_reflecting μ₀
  have hΦmeas : Measurable Φ := hemb.measurable
  obtain ⟨Ψ, hΨmeas, hΨΦ⟩ :=
    hemb.exists_measurable_extend measurable_id (fun _ => ‹Nonempty X›)
  have hΨΦx : ∀ x, Ψ (Φ x) = x := fun x => congrFun hΨΦ x
  -- pushforwards
  set ν : ℕ → Measure ℝ := fun n => Measure.map Φ (μ n : Measure X) with hν
  set ν₀ : Measure ℝ := Measure.map Φ (μ₀ : Measure X) with hν₀
  set lam : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1) with hlam
  have hraw : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
      AEMeasurable (quantile ρ) lam := by
    intro ρ hρ
    letI := hρ
    dsimp [lam]
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact aemeasurable_quantile_restrict_Ioo
  let Q : ℕ → ℝ → ℝ := fun n => (hraw (ν n) inferInstance).mk (quantile (ν n))
  let Q₀ : ℝ → ℝ := (hraw ν₀ inferInstance).mk (quantile ν₀)
  have hQmeas : ∀ n, Measurable (Q n) := fun n => (hraw (ν n) inferInstance).measurable_mk
  have hQ₀meas : Measurable Q₀ := (hraw ν₀ inferInstance).measurable_mk
  have hQeq : ∀ n, quantile (ν n) =ᵐ[lam] Q n := fun n =>
    (hraw (ν n) inferInstance).ae_eq_mk
  have hQ₀eq : quantile ν₀ =ᵐ[lam] Q₀ := (hraw ν₀ inferInstance).ae_eq_mk
  have hQlaw : ∀ n, Measure.map (Q n) lam = ν n := by
    intro n
    rw [← Measure.map_congr (hQeq n)]
    dsimp [lam]
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact map_quantile_volume_Ioo
  have hQ₀law : Measure.map Q₀ lam = ν₀ := by
    rw [← Measure.map_congr hQ₀eq]
    dsimp [lam]
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact map_quantile_volume_Ioo
  set Y : ℕ → ℝ → X := fun n u => Ψ (Q n u) with hY
  set Y₀ : ℝ → X := fun u => Ψ (Q₀ u) with hY₀
  have hconv : ∀ t : ℝ, ν₀ {t} = 0 →
      Filter.Tendsto (fun n => ProbabilityTheory.cdf (ν n) t) Filter.atTop
        (nhds (ProbabilityTheory.cdf ν₀ t)) := by
    intro t ht
    exact tendsto_cdf_map_of_null_atom μ μ₀ hμ Φ hΦmeas hdiscont t ht
  have hmeas : ∀ n, Measurable (Y n) := fun n => hΨmeas.comp (hQmeas n)
  have hmeas0 : Measurable Y₀ := hΨmeas.comp hQ₀meas
  have hlaw : ∀ n, Measure.map (Y n) lam = (μ n : Measure X) := by
    intro n
    change Measure.map (Ψ ∘ Q n) lam = _
    rw [← Measure.map_map hΨmeas (hQmeas n), hQlaw]
    change Measure.map Ψ (Measure.map Φ (μ n : Measure X)) = _
    rw [Measure.map_map hΨmeas hΦmeas, hΨΦ, Measure.map_id]
  have hlaw0 : Measure.map Y₀ lam = (μ₀ : Measure X) := by
    change Measure.map (Ψ ∘ Q₀) lam = _
    rw [← Measure.map_map hΨmeas hQ₀meas, hQ₀law]
    change Measure.map Ψ (Measure.map Φ (μ₀ : Measure X)) = _
    rw [Measure.map_map hΨmeas hΦmeas, hΨΦ, Measure.map_id]
  have hrange : ∀ n, ∀ᵐ u ∂lam, ∃ z, Φ z = Q n u := by
    intro n
    have h1 : ∀ᵐ y ∂(Measure.map Φ (μ n : Measure X)), ∃ x, Φ x = y := by
      rw [ae_map_iff hΦmeas.aemeasurable hemb.measurableSet_range]
      exact Filter.Eventually.of_forall (fun x => ⟨x, rfl⟩)
    change ∀ᵐ y ∂(ν n), ∃ x, Φ x = y at h1
    rw [← hQlaw n, ae_map_iff (hQmeas n).aemeasurable hemb.measurableSet_range] at h1
    exact h1
  have hrange0 : ∀ᵐ u ∂lam, ∃ z, Φ z = Q₀ u := by
    have h1 : ∀ᵐ y ∂(Measure.map Φ (μ₀ : Measure X)), ∃ x, Φ x = y := by
      rw [ae_map_iff hΦmeas.aemeasurable hemb.measurableSet_range]
      exact Filter.Eventually.of_forall (fun x => ⟨x, rfl⟩)
    change ∀ᵐ y ∂ν₀, ∃ x, Φ x = y at h1
    rw [← hQ₀law, ae_map_iff hQ₀meas.aemeasurable hemb.measurableSet_range] at h1
    exact h1
  have haeQ : ∀ᵐ u ∂lam, Filter.Tendsto (fun n => quantile (ν n) u) Filter.atTop
      (nhds (quantile ν₀ u)) :=
    ae_tendsto_quantile ν ν₀ hconv
  have hae : ∀ᵐ u ∂lam, Filter.Tendsto (fun n => Y n u) Filter.atTop (nhds (Y₀ u)) := by
    filter_upwards [haeQ, ae_all_iff.mpr hQeq, hQ₀eq,
      ae_all_iff.mpr hrange, hrange0] with u hQQ hEq hEq0 hmem_n hmem_0
    have hQQ : Filter.Tendsto (fun n => Q n u) Filter.atTop (nhds (Q₀ u)) := by
      simpa only [hEq, hEq0] using hQQ
    choose z hz using (fun n => hmem_n n)
    obtain ⟨z0, hz0⟩ := hmem_0
    -- Φ (Y n u) = Q_n u
    have e1 : ∀ n, Φ (Y n u) = Q n u := by
      intro n
      have hzn : Φ (z n) = Q n u := hz n
      have hYz : Y n u = z n := by
        change Ψ (Q n u) = z n
        rw [← hzn, hΨΦx]
      rw [hYz, hzn]
    have e0 : Φ (Y₀ u) = Q₀ u := by
      have hYz0 : Y₀ u = z0 := by
        change Ψ (Q₀ u) = z0
        rw [← hz0, hΨΦx]
      rw [hYz0, hz0]
    have hQQ' : Filter.Tendsto (fun n => Φ (Y n u)) Filter.atTop (nhds (Φ (Y₀ u))) := by
      rw [show (fun n => Φ (Y n u)) = (fun n => Q n u) from funext e1,
        e0]
      exact hQQ
    exact hrefl (fun n => Y n u) (Y₀ u) hQQ'
  exact ⟨Y, Y₀, hmeas, hmeas0, hlaw, hlaw0, hae⟩

end D5.S3.Analytic.Probability.SkorokhodRepresentation
end
