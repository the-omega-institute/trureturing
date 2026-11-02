/- GID: D5/S3/Analytic/Probability/CompactConvexOrder
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/CompactConvexOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: CompactConvexOrder for compact scalar martingale transport. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import D5.S3.Analytic.Probability.CompactQuantile
import D5.S3.Analytic.Convexity.FiniteMajorization
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure


open MeasureTheory Set Filter Topology

namespace Econlib.Probability
abbrev ProbDist (α : Type*) [MeasurableSpace α] := ProbabilityMeasure α
namespace ProbDist
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
noncomputable def expect (d : ProbDist α) (f : α → ℝ) : ℝ := ∫ x, f x ∂d.toMeasure
noncomputable def map (d : ProbDist α) (f : α → β) (_hf : Measurable f) : ProbDist β :=
  ProbabilityMeasure.map d f
@[simp] lemma map_toMeasure (d : ProbDist α) (f : α → β) (hf : Measurable f) :
    ((map d f hf : ProbDist β) : Measure β) = Measure.map f d.toMeasure := rfl
lemma expect_map (d : ProbDist α) (f : α → β) (hf : Measurable f) (g : β → ℝ)
    (hg : AEStronglyMeasurable g ((map d f hf : ProbDist β).toMeasure)) :
    (map d f hf).expect g = d.expect (fun x => g (f x)) := by
  simp [expect, map, MeasureTheory.integral_map hf.aemeasurable hg]
def supportsOn {α : Type*} [MeasurableSpace α] (d : ProbDist α) (s : Set α) : Prop :=
  d.toMeasure s = 1
lemma ae_mem_of_supportsOn {d : ProbDist ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (h : d.supportsOn s) : ∀ᵐ x ∂d.toMeasure, x ∈ s :=
  (ae_mem_iff_measure_eq hs.nullMeasurableSet).mpr (h.trans (measure_univ).symm)
lemma integrable_of_supportsOn_Icc {d : ProbDist ℝ} {a b : ℝ} {f : ℝ → ℝ}
    (h : d.supportsOn (Set.Icc a b)) (hf : ContinuousOn f (Set.Icc a b)) :
    Integrable f d.toMeasure := by
  have hind : Integrable ((Set.Icc a b).indicator f) d.toMeasure :=
    (hf.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hae : (fun x ↦ (Set.Icc a b).indicator f x) =ᵐ[d.toMeasure] f := by
    filter_upwards [d.ae_mem_of_supportsOn measurableSet_Icc h] with x hx
    simp [hx]
  exact (integrable_congr hae).mp hind
lemma integrable_id_of_supportsOn_Icc {d : ProbDist ℝ} {a b : ℝ}
    (h : d.supportsOn (Set.Icc a b)) : Integrable id d.toMeasure :=
  d.integrable_of_supportsOn_Icc h continuousOn_id
end ProbDist
structure ConvexOrderOnIcc (a b : ℝ) (μ ν : ProbDist ℝ) : Prop where
  support_left : μ.supportsOn (Set.Icc a b)
  support_right : ν.supportsOn (Set.Icc a b)
  mean_eq : μ.expect id = ν.expect id
  convex_expect_le : ∀ φ : ℝ → ℝ, ConvexOn ℝ (Set.Icc a b) φ → ContinuousOn φ (Set.Icc a b) →
    μ.expect φ ≤ ν.expect φ
notation:50 μ " ≼cx[" a "," b "] " ν => ConvexOrderOnIcc a b μ ν
end Econlib.Probability

section
open MeasureTheory Set Filter Topology

noncomputable section

namespace MeasureTheory.Measure

variable {μ : Measure ℝ}

/-- The hinge function `x ↦ max (x - z) 0` is continuous. -/
private lemma continuous_hinge (z : ℝ) : Continuous (fun x : ℝ => max (x - z) 0) :=
  (continuous_id.sub continuous_const).max continuous_const

/-- Pushforward identity for the stop-loss: Integrating the hinge against `μ` equals integrating
`max (quantile μ u - z) 0` against Lebesgue on `Ioo 0 1`. -/
private lemma stopLoss_eq_integral_hinge_quantile [IsProbabilityMeasure μ] (z : ℝ) :
    stopLoss μ z = ∫ u in Ioo (0 : ℝ) 1, max (quantile μ u - z) 0 := by
  unfold stopLoss
  exact integral_eq_integral_quantile (fun x => max (x - z) 0)
    (continuous_hinge z).aestronglyMeasurable

/-- `Ioo 0 1 =ᵐ[volume] Ioc 0 t ∪ Ioc t 1` when `0 ≤ t ≤ 1`. -/
private lemma Ioo_01_ae_eq_union {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Ioc (0 : ℝ) t ∪ Ioc t 1 : Set ℝ) := by
  have h_union_eq : (Ioc (0 : ℝ) t ∪ Ioc t 1 : Set ℝ) = Ioc (0 : ℝ) 1 :=
    Ioc_union_Ioc_eq_Ioc ht0 ht1
  rw [h_union_eq]
  exact Ioo_ae_eq_Ioc

/-- `Ioc 0 1 =ᵐ[volume] Ioo 0 1`. -/
private lemma Ioc_01_ae_eq_Ioo : (Ioc (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Ioo (0 : ℝ) 1 : Set ℝ) :=
  Ioo_ae_eq_Ioc.symm

/-- If `id` is `μ`-integrable, then `max (quantile μ · - z) 0` is integrable on `Ioo 0 1`. -/
private lemma integrable_hinge_quantile [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) (z : ℝ) :
    IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioo (0 : ℝ) 1) volume := by
  have h1 : Integrable (fun x : ℝ => max (x - z) 0) μ :=
    stopLoss_integrable hμ_int z
  have h_map : Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) = μ :=
    map_quantile_volume_Ioo
  have hqae : AEMeasurable (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    aemeasurable_quantile_restrict_Ioo
  rw [← h_map] at h1
  rwa [integrable_map_measure (continuous_hinge z).aestronglyMeasurable hqae] at h1

/-- If `id` is `μ`-integrable, then `quantile μ` is integrable on `Ioo 0 1`. -/
private lemma integrable_quantile_Ioo [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) :
    IntegrableOn (quantile μ) (Ioo (0 : ℝ) 1) volume := by
  have h_map : Measure.map (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) = μ :=
    map_quantile_volume_Ioo
  have hqae : AEMeasurable (quantile μ) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    aemeasurable_quantile_restrict_Ioo
  have hid_sm : AEStronglyMeasurable (fun x : ℝ => x) μ :=
    aestronglyMeasurable_id
  rw [← h_map] at hμ_int hid_sm
  rw [integrable_map_measure hid_sm hqae] at hμ_int
  exact hμ_int

/-- `Ioc t 1 ⊆ᵐ[volume] Ioo 0 1` when `0 ≤ t`. -/
private lemma Ioc_t_one_ae_le_Ioo_01 {t : ℝ} (ht0 : 0 ≤ t) :
    (Ioc t 1 : Set ℝ) ≤ᵐ[volume] (Ioo (0 : ℝ) 1 : Set ℝ) := by
  -- The symmetric difference is contained in {1}, which has measure zero.
  have h_diff : {u : ℝ | u ∈ Ioc t 1 ∧ u ∉ Ioo (0 : ℝ) 1} ⊆ {1} := by
    intro u hu
    obtain ⟨hu_Ioc, hu_notIoo⟩ := hu
    obtain ⟨hu1, hu2⟩ := hu_Ioc
    simp only [mem_Ioo, not_and, not_lt] at hu_notIoo
    have hpos : 0 < u := lt_of_le_of_lt ht0 hu1
    exact mem_singleton_iff.mpr (le_antisymm hu2 (hu_notIoo hpos))
  have h_null : volume {u : ℝ | u ∈ Ioc t 1 ∧ u ∉ Ioo (0 : ℝ) 1} = 0 :=
    measure_mono_null h_diff (by rw [Real.volume_singleton])
  rw [ae_le_set]
  apply measure_mono_null ?_ h_null
  intro u hu
  exact hu

/-- `Ioc 0 1 ⊆ᵐ[volume] Ioo 0 1`. -/
private lemma Ioc_01_ae_le_Ioo_01 :
    (Ioc (0 : ℝ) 1 : Set ℝ) ≤ᵐ[volume] (Ioo (0 : ℝ) 1 : Set ℝ) :=
  Ioc_t_one_ae_le_Ioo_01 le_rfl

/-- On `Ioc t 1` (for `0 ≤ t`), the hinge-quantile is integrable. -/
private lemma integrable_hinge_quantile_Ioc [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht0 : 0 ≤ t) (z : ℝ) :
    IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioc t 1) volume :=
  (integrable_hinge_quantile hμ_int (μ := μ) z).mono_set_ae
    (Ioc_t_one_ae_le_Ioo_01 ht0)

/-- On `Ioc 0 t` (for `t < 1`), the hinge-quantile is integrable. -/
private lemma integrable_hinge_quantile_Ioc_0_t [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht1 : t < 1) (z : ℝ) :
    IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioc (0 : ℝ) t) volume := by
  refine (integrable_hinge_quantile hμ_int (μ := μ) z).mono_set ?_
  intro u hu
  exact ⟨hu.1, lt_of_le_of_lt hu.2 ht1⟩

/-- On `Ioc t 1` (for `0 ≤ t`), the quantile function is integrable. -/
private lemma integrable_quantile_Ioc [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht0 : 0 ≤ t) :
    IntegrableOn (quantile μ) (Ioc t 1) volume :=
  (integrable_quantile_Ioo hμ_int (μ := μ)).mono_set_ae
    (Ioc_t_one_ae_le_Ioo_01 ht0)

/-- On `Ioc 0 t` (for `t < 1`), the quantile is integrable. -/
private lemma integrable_quantile_Ioc_0_t [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht1 : t < 1) :
    IntegrableOn (quantile μ) (Ioc (0 : ℝ) t) volume := by
  refine (integrable_quantile_Ioo hμ_int (μ := μ)).mono_set ?_
  intro u hu
  exact ⟨hu.1, lt_of_le_of_lt hu.2 ht1⟩

private lemma volume_real_Ioc_t_one {t : ℝ} (ht : t ≤ 1) :
    volume.real (Ioc t 1) = 1 - t :=
  Real.volume_real_Ioc_of_le ht

/-- The integral of the constant `z` over `Ioc t 1` (for `t ≤ 1`) is `z · (1 - t)`. -/
private lemma setIntegral_const_Ioc_t_one {t : ℝ} (ht : t ≤ 1) (z : ℝ) :
    ∫ _ in Ioc t 1, (z : ℝ) = z * (1 - t) := by
  rw [setIntegral_const, volume_real_Ioc_t_one ht, smul_eq_mul]
  ring

private lemma integrable_const_Ioo_01 (z : ℝ) :
    IntegrableOn (fun _ : ℝ => z) (Ioo (0 : ℝ) 1) volume := by
  refine integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) ?_
  exact enorm_ne_top

private lemma integrable_const_Ioc_t_one {t : ℝ} (z : ℝ) :
    IntegrableOn (fun _ : ℝ => z) (Ioc t 1) volume := by
  refine integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) ?_
  exact enorm_ne_top

/-- Split the integral of the hinge-quantile over `Ioo 0 1` into integrals over `Ioc 0 t` and
`Ioc t 1` (for `0 < t ≤ 1`). -/
private lemma integral_hinge_quantile_Ioo_split [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (z : ℝ) :
    ∫ u in Ioo (0 : ℝ) 1, max (quantile μ u - z) 0 =
      (∫ u in Ioc (0 : ℝ) t, max (quantile μ u - z) 0) +
        (∫ u in Ioc t 1, max (quantile μ u - z) 0) := by
  have h_ae : (Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Ioc (0 : ℝ) t ∪ Ioc t 1 : Set ℝ) :=
    Ioo_01_ae_eq_union ht0.le ht1
  rw [setIntegral_congr_set h_ae]
  have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioc t 1) := Set.Ioc_disjoint_Ioc_of_le le_rfl
  have h1 : IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioc (0 : ℝ) t) volume := by
    rcases eq_or_lt_of_le ht1 with ht1_eq | ht1_lt
    · subst ht1_eq
      exact (integrable_hinge_quantile hμ_int (μ := μ) z).mono_set_ae
        Ioc_01_ae_le_Ioo_01
    · exact integrable_hinge_quantile_Ioc_0_t hμ_int ht1_lt z
  have h2 : IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioc t 1) volume :=
    integrable_hinge_quantile_Ioc hμ_int ht0.le z
  exact setIntegral_union hdisj measurableSet_Ioc h1 h2

/-- Split the integral of `quantile μ` over `Ioo 0 1` into integrals over `Ioc 0 t` and `Ioc t 1`
(for `0 < t ≤ 1`). -/
private theorem integral_quantile_Ioo_split [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∫ u in Ioo (0 : ℝ) 1, quantile μ u =
      (∫ u in Ioc (0 : ℝ) t, quantile μ u) +
        (∫ u in Ioc t 1, quantile μ u) := by
  have h_ae : (Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Ioc (0 : ℝ) t ∪ Ioc t 1 : Set ℝ) :=
    Ioo_01_ae_eq_union ht0.le ht1
  rw [setIntegral_congr_set h_ae]
  have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioc t 1) := Set.Ioc_disjoint_Ioc_of_le le_rfl
  have h1 : IntegrableOn (quantile μ) (Ioc (0 : ℝ) t) volume := by
    rcases eq_or_lt_of_le ht1 with ht1_eq | ht1_lt
    · subst ht1_eq
      exact (integrable_quantile_Ioo hμ_int (μ := μ)).mono_set_ae
        Ioc_01_ae_le_Ioo_01
    · exact integrable_quantile_Ioc_0_t hμ_int ht1_lt
  have h2 : IntegrableOn (quantile μ) (Ioc t 1) volume :=
    integrable_quantile_Ioc hμ_int ht0.le
  exact setIntegral_union hdisj measurableSet_Ioc h1 h2

/-- **Universal upper bound (Legendre):** For any `z ∈ ℝ`,
`∫ u in Ioc t 1, quantile μ u ≤ stopLoss μ z + z · (1 - t)`. -/
private theorem upperIntegratedQuantile_le_stopLoss_add [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    (∫ u in Ioc t 1, quantile μ u) ≤ stopLoss μ z + z * (1 - t) := by
  obtain ⟨ht0, ht1⟩ := ht
  -- Degenerate case t = 1: LHS = 0 and RHS ≥ 0.
  rcases eq_or_lt_of_le ht1 with ht1_eq | ht1_lt
  · have h_empty : (Ioc (1 : ℝ) 1 : Set ℝ) = ∅ := by
      ext x; simp only [mem_Ioc, mem_empty_iff_false, iff_false, not_and, not_le]
      intro h1; exact h1
    rw [ht1_eq, h_empty, setIntegral_empty, sub_self, mul_zero, add_zero]
    exact stopLoss_nonneg z
  -- Main case: 0 ≤ t < 1.
  rw [stopLoss_eq_integral_hinge_quantile]
  rcases eq_or_lt_of_le ht0 with ht0_eq | ht0_pos
  · -- t = 0 branch.
    subst ht0_eq
    rw [setIntegral_congr_set (s := Ioc (0 : ℝ) 1) (t := Ioo (0 : ℝ) 1) Ioc_01_ae_eq_Ioo]
    have h_quant_int : IntegrableOn (quantile μ) (Ioo (0 : ℝ) 1) volume :=
      integrable_quantile_Ioo hμ_int
    have h_hinge_int : IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioo (0 : ℝ) 1) volume :=
      integrable_hinge_quantile hμ_int z
    have h_const : IntegrableOn (fun _ : ℝ => z) (Ioo (0 : ℝ) 1) volume :=
      integrable_const_Ioo_01 z
    have h_pointwise : ∀ u ∈ Ioo (0 : ℝ) 1,
        quantile μ u ≤ max (quantile μ u - z) 0 + z := fun u _ => by
      linarith [le_max_left (quantile μ u - z) 0]
    have h_sum_int : IntegrableOn
        (fun u => max (quantile μ u - z) 0 + z) (Ioo (0 : ℝ) 1) volume :=
      h_hinge_int.add h_const
    have h_mono := setIntegral_mono_on h_quant_int h_sum_int measurableSet_Ioo h_pointwise
    rw [integral_add h_hinge_int h_const] at h_mono
    have h_const_int : ∫ _ in Ioo (0 : ℝ) 1, (z : ℝ) = z := by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le (zero_le_one), sub_zero, one_smul]
    rw [h_const_int] at h_mono
    linarith
  -- Main case: 0 < t < 1.
  rw [integral_hinge_quantile_Ioo_split hμ_int ht0_pos ht1_lt.le z]
  have h1 : (∫ u in Ioc t 1, quantile μ u) ≤
      (∫ u in Ioc t 1, max (quantile μ u - z) 0) + z * (1 - t) := by
    have h_quant_int_Ioc : IntegrableOn (quantile μ) (Ioc t 1) volume :=
      integrable_quantile_Ioc hμ_int ht0
    have h_hinge_int_Ioc : IntegrableOn
        (fun u => max (quantile μ u - z) 0) (Ioc t 1) volume :=
      integrable_hinge_quantile_Ioc hμ_int ht0 z
    have h_const_Ioc : IntegrableOn (fun _ : ℝ => z) (Ioc t 1) volume :=
      integrable_const_Ioc_t_one z
    have h_pointwise : ∀ u ∈ Ioc t 1, quantile μ u ≤ max (quantile μ u - z) 0 + z :=
      fun u _ => by linarith [le_max_left (quantile μ u - z) 0]
    have h_sum : IntegrableOn (fun u => max (quantile μ u - z) 0 + z) (Ioc t 1) volume :=
      h_hinge_int_Ioc.add h_const_Ioc
    have h_mono := setIntegral_mono_on h_quant_int_Ioc h_sum measurableSet_Ioc h_pointwise
    rw [integral_add h_hinge_int_Ioc h_const_Ioc] at h_mono
    rw [setIntegral_const_Ioc_t_one ht1_lt.le z] at h_mono
    exact h_mono
  have h2 : 0 ≤ ∫ u in Ioc (0 : ℝ) t, max (quantile μ u - z) 0 :=
    integral_nonneg (fun _ => le_max_right _ _)
  linarith

/-- **Equality at `z = quantile μ t`:** the Legendre conjugate is attained. -/
private theorem upperIntegratedQuantile_eq_stopLoss_add [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ u in Ioc t 1, quantile μ u) =
        stopLoss μ (quantile μ t) + (quantile μ t) * (1 - t) := by
  obtain ⟨ht0, ht1⟩ := ht
  set z := quantile μ t with hz_def
  rw [stopLoss_eq_integral_hinge_quantile]
  rw [integral_hinge_quantile_Ioo_split hμ_int ht0 ht1.le z]
  -- Piece A: ∫ Ioc 0 t, max (q u - z) 0 = 0.
  have hA : ∫ u in Ioc (0 : ℝ) t, max (quantile μ u - z) 0 = 0 := by
    have h_ae : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) t)),
        max (quantile μ u - z) 0 = 0 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      obtain ⟨hu0, hu_le⟩ := hu
      have hu_in : u ∈ Ioo (0 : ℝ) 1 := ⟨hu0, lt_of_le_of_lt hu_le ht1⟩
      have ht_in : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
      have hq_le : quantile μ u ≤ quantile μ t := monotoneOn_quantile hu_in ht_in hu_le
      have hdiff_le : quantile μ u - z ≤ 0 := by rw [hz_def]; linarith
      exact max_eq_right hdiff_le
    -- The integrand is ae zero, so the integral collapses to `∫ 0 = 0`.
    rw [integral_congr_ae h_ae, integral_zero]
  -- Piece B: ∫ Ioc t 1, max (q u - z) 0 = ∫ Ioc t 1, (q u - z).
  have hB : ∫ u in Ioc t 1, max (quantile μ u - z) 0 =
      ∫ u in Ioc t 1, (quantile μ u - z) := by
    have h_ae : ∀ᵐ u ∂(volume.restrict (Ioc t 1)),
        max (quantile μ u - z) 0 = quantile μ u - z := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [Measure.ae_ne (volume : Measure ℝ) 1] with u hu_ne hu_in
      obtain ⟨hu_gt, hu_le⟩ := hu_in
      have hu_lt : u < 1 := lt_of_le_of_ne hu_le hu_ne
      have hu_in_Ioo : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le ht0 hu_gt.le, hu_lt⟩
      have ht_in : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
      have hq_ge : quantile μ t ≤ quantile μ u :=
        monotoneOn_quantile ht_in hu_in_Ioo hu_gt.le
      have hdiff_ge : 0 ≤ quantile μ u - z := by rw [hz_def]; linarith
      exact max_eq_left hdiff_ge
    exact integral_congr_ae h_ae
  rw [hA, hB, zero_add]
  have h_quant_int_Ioc : IntegrableOn (quantile μ) (Ioc t 1) volume :=
    integrable_quantile_Ioc hμ_int ht0.le
  have h_const_Ioc : IntegrableOn (fun _ : ℝ => z) (Ioc t 1) volume :=
    integrable_const_Ioc_t_one z
  rw [integral_sub h_quant_int_Ioc h_const_Ioc, setIntegral_const_Ioc_t_one ht1.le z]
  ring

end MeasureTheory.Measure

end
end

section
noncomputable section

open MeasureTheory Set

namespace Econlib.Probability

/-- The hinge/stop-loss test function `x ↦ max (x - z) 0` is convex on any set. -/
private lemma convexOn_hinge_on (a b z : ℝ) :
    ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => max (x - z) 0) := by
  have h_univ : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => max (x - z) 0) :=
    convexOn_hinge_right z
  exact h_univ.subset (subset_univ _) (convex_Icc a b)

/-- The hinge test function is continuous. -/
private lemma continuous_hinge (z : ℝ) : Continuous (fun x : ℝ => max (x - z) 0) :=
  (continuous_id.sub continuous_const).max continuous_const

/-- **Stop-loss monotonicity under convex order.** If `μ ≼cx[a,b] ν`, then the stop-loss function
of `μ` is pointwise bounded by the stop-loss function of `ν`. -/
private lemma stopLoss_le_of_convexOrderOnIcc {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) (z : ℝ) :
    μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z := by
  -- `stopLoss d z = d.expect (fun x => max (x - z) 0)`; apply `h.convex_expect_le`.
  have hconv : ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => max (x - z) 0) :=
    convexOn_hinge_on a b z
  have hcont : ContinuousOn (fun x : ℝ => max (x - z) 0) (Set.Icc a b) :=
    (continuous_hinge z).continuousOn
  have hexpect := h.convex_expect_le _ hconv hcont
  exact hexpect

/-- **Upper integrated-quantile inequality under convex order.** For compact-supported
`μ ≼cx[a,b] ν` and `t ∈ (0, 1]`, the upper integrated quantile of `μ` is at most that of `ν`. -/
private theorem upperIntegratedQuantile_le_of_convexOrderOnIcc {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) ≤
    (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u) := by
  obtain ⟨ht0, ht1⟩ := ht
  -- Handle t = 1 degenerately.
  rcases eq_or_lt_of_le ht1 with ht1_eq | ht1_lt
  · subst ht1_eq
    rw [Set.Ioc_self, setIntegral_empty, setIntegral_empty]
  -- Main case: 0 < t < 1.
  set z := MeasureTheory.Measure.quantile ν.toMeasure t with hz_def
  -- Integrability of `id` for μ and ν from compact support on `[a, b]`.
  have hμ_int : Integrable (fun x : ℝ => x) μ.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_left
  have hν_int : Integrable (fun x : ℝ => x) ν.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_right
  have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
  have ht_Ioo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht1_lt⟩
  -- Step 1: universal bound for μ at z.
  have h_step1 : (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) ≤
      μ.toMeasure.stopLoss z + z * (1 - t) :=
    MeasureTheory.Measure.upperIntegratedQuantile_le_stopLoss_add hμ_int ht_Icc z
  -- Step 2: stop-loss monotonicity.
  have h_step2 : μ.toMeasure.stopLoss z ≤ ν.toMeasure.stopLoss z :=
    stopLoss_le_of_convexOrderOnIcc h z
  -- Step 3: equality for ν at z = quantile ν.toMeasure t.
  have h_step3 : ν.toMeasure.stopLoss z + z * (1 - t) =
      ∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u :=
    (MeasureTheory.Measure.upperIntegratedQuantile_eq_stopLoss_add hν_int ht_Ioo).symm
  -- Chain.
  linarith

/-- **Lower integrated-quantile inequality under convex order.** For compact-supported
`μ ≼cx[a,b] ν` and `t ∈ (0, 1]`, the lower integrated quantile of `ν` is at most that of `μ`. -/
theorem lowerIntegratedQuantile_ge_of_convexOrderOnIcc {a b : ℝ} {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (∫ u in Set.Ioc 0 t, MeasureTheory.Measure.quantile ν.toMeasure u) ≤
    (∫ u in Set.Ioc 0 t, MeasureTheory.Measure.quantile μ.toMeasure u) := by
  obtain ⟨ht0, ht1⟩ := ht
  -- Integrability of `id` for μ and ν from compact support on `[a, b]`.
  have hμ_int : Integrable (fun x : ℝ => x) μ.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_left
  have hν_int : Integrable (fun x : ℝ => x) ν.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc h.support_right
  -- Step: ∫ Ioo 0 1, q_μ = μ.expect id (via pushforward), similarly for ν. Then mean_eq gives
  -- ∫ Ioo 0 1, q_μ = ∫ Ioo 0 1, q_ν.
  -- Split each into Ioc 0 t + Ioc t 1 and use upper inequality on Ioc t 1.
  have h_mean_eq : μ.expect id = ν.expect id := h.mean_eq
  -- Use integral_eq_integral_quantile to compute expect id as ∫ Ioo 0 1, q.
  -- `expect id` equals the integrated quantile over `Ioo 0 1` (pushforward to the unit interval).
  have h_pushforward : ∀ d : ProbDist ℝ, d.expect id =
      ∫ u in Set.Ioo (0 : ℝ) 1, MeasureTheory.Measure.quantile d.toMeasure u := fun d => by
    unfold ProbDist.expect
    exact MeasureTheory.Measure.integral_eq_integral_quantile (fun x => x)
      aestronglyMeasurable_id
  have h_μ_pushforward := h_pushforward μ
  have h_ν_pushforward := h_pushforward ν
  -- Split the integral: ∫ Ioo 0 1 = ∫ Ioc 0 t + ∫ Ioc t 1.
  have h_split_μ : (∫ u in Set.Ioo (0 : ℝ) 1,
        MeasureTheory.Measure.quantile μ.toMeasure u) =
      (∫ u in Set.Ioc (0 : ℝ) t, MeasureTheory.Measure.quantile μ.toMeasure u) +
      (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) :=
    MeasureTheory.Measure.integral_quantile_Ioo_split hμ_int ht0 ht1
  have h_split_ν : (∫ u in Set.Ioo (0 : ℝ) 1,
        MeasureTheory.Measure.quantile ν.toMeasure u) =
      (∫ u in Set.Ioc (0 : ℝ) t, MeasureTheory.Measure.quantile ν.toMeasure u) +
      (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u) :=
    MeasureTheory.Measure.integral_quantile_Ioo_split hν_int ht0 ht1
  -- ∫ Ioo q_μ = ∫ Ioo q_ν.
  have h_total : (∫ u in Set.Ioo (0 : ℝ) 1,
        MeasureTheory.Measure.quantile μ.toMeasure u) =
      (∫ u in Set.Ioo (0 : ℝ) 1, MeasureTheory.Measure.quantile ν.toMeasure u) := by
    rw [← h_μ_pushforward, ← h_ν_pushforward, h_mean_eq]
  -- Upper inequality on Ioc t 1.
  have h_upper : (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile μ.toMeasure u) ≤
      (∫ u in Set.Ioc t 1, MeasureTheory.Measure.quantile ν.toMeasure u) :=
    upperIntegratedQuantile_le_of_convexOrderOnIcc h ⟨ht0, ht1⟩
  -- Combine: ∫ Ioc 0 t, q_μ = (∫ Ioo q_μ) - ∫ Ioc t 1, q_μ
  --                       = (∫ Ioo q_ν) - ∫ Ioc t 1, q_μ
  --                       ≥ (∫ Ioo q_ν) - ∫ Ioc t 1, q_ν
  --                       = ∫ Ioc 0 t, q_ν.
  linarith

end Econlib.Probability

end
end
