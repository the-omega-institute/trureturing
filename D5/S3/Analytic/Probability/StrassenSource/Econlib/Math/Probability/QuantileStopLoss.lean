/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.Probability.Quantile
public import D5.S3.Analytic.Probability.StrassenSource.Econlib.Math.Probability.StopLoss

/-!
# Legendre-type identities relating stop-loss and integrated quantile

For a probability measure `μ` on `ℝ` with finite first moment, the **stop-loss function** and the
**upper integrated quantile** are related by a Legendre-Fenchel-type pair:

`∫ u in Ioc t 1, quantile μ u ≤ stopLoss μ z + z · (1 - t)`      (universal bound)

with equality at `z = quantile μ t`:

`∫ u in Ioc t 1, quantile μ u = stopLoss μ (quantile μ t) + (quantile μ t) · (1 - t)`.

## Main statements

* `Measure.upperIntegratedQuantile_le_stopLoss_add` — universal upper bound, for `t ∈ Icc 0 1`.
* `Measure.upperIntegratedQuantile_eq_stopLoss_add` — equality at `z = quantile μ t`, for
  `t ∈ Ioo 0 1`.
* `Measure.integral_quantile_Ioo_split` — additivity of the quantile integral across `Ioc 0 t` and
  `Ioc t 1`.

## Notes

The pushforward identity `stopLoss μ z = ∫ u in Ioo 0 1, max (quantile μ u - z) 0` reduces both
statements to estimates on the quantile transform; monotonicity of `quantile μ` on `(0, 1)`
supplies the equality case.

## Tags

stop-loss, quantile, legendre transform, convex conjugate
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace MeasureTheory.Measure

variable {μ : Measure ℝ}

/-! ### Hinge-quantile pushforward identity -/

/-- The hinge function `x ↦ max (x - z) 0` is continuous. -/
private lemma continuous_hinge (z : ℝ) : Continuous (fun x : ℝ => max (x - z) 0) :=
  (continuous_id.sub continuous_const).max continuous_const

/-- Pushforward identity for the stop-loss: Integrating the hinge against `μ` equals integrating
`max (quantile μ u - z) 0` against Lebesgue on `Ioo 0 1`. -/
lemma stopLoss_eq_integral_hinge_quantile [IsProbabilityMeasure μ] (z : ℝ) :
    stopLoss μ z = ∫ u in Ioo (0 : ℝ) 1, max (quantile μ u - z) 0 := by
  unfold stopLoss
  exact integral_eq_integral_quantile (fun x => max (x - z) 0)
    (continuous_hinge z).aestronglyMeasurable

/-! ### AE-equality of `Ioo 0 1` with `Ioc 0 t ∪ Ioc t 1` -/

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

/-! ### Integrability of hinge-quantile on subintervals -/

/-- If `id` is `μ`-integrable, then `max (quantile μ · - z) 0` is integrable on `Ioo 0 1`. -/
lemma integrable_hinge_quantile [IsProbabilityMeasure μ]
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
lemma integrable_quantile_Ioo [IsProbabilityMeasure μ]
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
lemma integrable_hinge_quantile_Ioc [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht0 : 0 ≤ t) (z : ℝ) :
    IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioc t 1) volume :=
  (integrable_hinge_quantile hμ_int (μ := μ) z).mono_set_ae
    (Ioc_t_one_ae_le_Ioo_01 ht0)

/-- On `Ioc 0 t` (for `t < 1`), the hinge-quantile is integrable. -/
lemma integrable_hinge_quantile_Ioc_0_t [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht1 : t < 1) (z : ℝ) :
    IntegrableOn (fun u => max (quantile μ u - z) 0) (Ioc (0 : ℝ) t) volume := by
  refine (integrable_hinge_quantile hμ_int (μ := μ) z).mono_set ?_
  intro u hu
  exact ⟨hu.1, lt_of_le_of_lt hu.2 ht1⟩

/-- On `Ioc t 1` (for `0 ≤ t`), the quantile function is integrable. -/
lemma integrable_quantile_Ioc [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht0 : 0 ≤ t) :
    IntegrableOn (quantile μ) (Ioc t 1) volume :=
  (integrable_quantile_Ioo hμ_int (μ := μ)).mono_set_ae
    (Ioc_t_one_ae_le_Ioo_01 ht0)

/-- On `Ioc 0 t` (for `t < 1`), the quantile is integrable. -/
lemma integrable_quantile_Ioc_0_t [IsProbabilityMeasure μ]
    (hμ_int : Integrable (fun x : ℝ => x) μ) {t : ℝ} (ht1 : t < 1) :
    IntegrableOn (quantile μ) (Ioc (0 : ℝ) t) volume := by
  refine (integrable_quantile_Ioo hμ_int (μ := μ)).mono_set ?_
  intro u hu
  exact ⟨hu.1, lt_of_le_of_lt hu.2 ht1⟩

/-! ### Volume of `Ioc t 1` when `t ≤ 1` -/

private lemma volume_real_Ioc_t_one {t : ℝ} (ht : t ≤ 1) :
    volume.real (Ioc t 1) = 1 - t :=
  Real.volume_real_Ioc_of_le ht

/-- The integral of the constant `z` over `Ioc t 1` (for `t ≤ 1`) is `z · (1 - t)`. -/
private lemma setIntegral_const_Ioc_t_one {t : ℝ} (ht : t ≤ 1) (z : ℝ) :
    ∫ _ in Ioc t 1, (z : ℝ) = z * (1 - t) := by
  rw [setIntegral_const, volume_real_Ioc_t_one ht, smul_eq_mul]
  ring

/-! ### Constant function integrability on `Ioo 0 1` and `Ioc t 1` -/

private lemma integrable_const_Ioo_01 (z : ℝ) :
    IntegrableOn (fun _ : ℝ => z) (Ioo (0 : ℝ) 1) volume := by
  refine integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) ?_
  exact enorm_ne_top

private lemma integrable_const_Ioc_t_one {t : ℝ} (z : ℝ) :
    IntegrableOn (fun _ : ℝ => z) (Ioc t 1) volume := by
  refine integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) ?_
  exact enorm_ne_top

/-! ### Split `Ioo 0 1` integral into two pieces -/

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
theorem integral_quantile_Ioo_split [IsProbabilityMeasure μ]
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

/-! ### Main lemmas: Universal bound -/

/-- **Universal upper bound (Legendre):** For any `z ∈ ℝ`,
`∫ u in Ioc t 1, quantile μ u ≤ stopLoss μ z + z · (1 - t)`. -/
theorem upperIntegratedQuantile_le_stopLoss_add [IsProbabilityMeasure μ]
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

/-! ### Main lemma: Equality case -/

/-- **Equality at `z = quantile μ t`:** the Legendre conjugate is attained. -/
theorem upperIntegratedQuantile_eq_stopLoss_add [IsProbabilityMeasure μ]
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
