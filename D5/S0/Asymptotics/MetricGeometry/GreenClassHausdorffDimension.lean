/- GID: D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension
   generality: G
   mirror-B: D5/B/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For a finite nontrivial discrete alphabet O, the PiNat naming space has Hausdorff dimension log base 2 of card O; its critical Hausdorff measure is the uniform string measure, and every finite-support green class has the same Hausdorff dimension. The proof establishes the mass-distribution bound from least differing coordinates and the reverse measure bound from finite prefix-cylinder covers. The varying-marginal generalization is not covered. -/

import D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter

open MeasureTheory Measure
open scoped ENNReal Topology
open Filter

namespace D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension

open D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter
open D5.S0.Naming.GreenClassMeasure

noncomputable section

attribute [local instance] PiNat.metricSpace PiNat.boundedSpace Pi.borelSpace

/-- The critical exponent of the uniform naming space over `O`. -/
noncomputable def namingDim (O : Type*) [Fintype O] : ℝ :=
  Real.logb 2 (Fintype.card O)

private theorem mem_greenClass_iff {O : Type*} {S : Finset ℕ} {t x : ℕ → O} :
    x ∈ greenClass S t ↔ ∀ i ∈ S, x i = t i := by
  simp [greenClass]

private noncomputable instance instIsProbabilityMeasureStringMeasure {O : Type*} [Fintype O]
    [Nonempty O] [MeasurableSpace O] : IsProbabilityMeasure (stringMeasure O) := by
  rw [stringMeasure]
  infer_instance

private theorem namingDim_nonneg {O : Type*} [Fintype O] [Nontrivial O] :
    0 ≤ namingDim O := by
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.one_lt_card.le)

private theorem two_rpow_namingDim {O : Type*} [Fintype O] [Nonempty O] :
    (2 : ℝ≥0∞) ^ namingDim O = Fintype.card O := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, namingDim,
    ENNReal.ofReal_rpow_of_pos (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast Fintype.card_pos)]
  norm_num

private theorem inv_card_pow_eq_half_pow_rpow {O : Type*} [Fintype O] [Nonempty O]
    (m : ℕ) :
    ((Fintype.card O : ℝ≥0∞))⁻¹ ^ m =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ^ namingDim O := by
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  calc
    ((Fintype.card O : ℝ≥0∞))⁻¹ ^ m =
        ((Fintype.card O : ℝ≥0∞))⁻¹ ^ (m : ℝ) :=
      (ENNReal.rpow_natCast _ _).symm
    _ = (((2 : ℝ≥0∞) ^ namingDim O)⁻¹) ^ (m : ℝ) := by
      rw [two_rpow_namingDim]
    _ = (((2 : ℝ≥0∞)⁻¹) ^ namingDim O) ^ (m : ℝ) := by
      congr 1
      exact (ENNReal.inv_rpow (2 : ℝ≥0∞) (namingDim O)).symm
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (namingDim O * (m : ℝ)) := by
      rw [ENNReal.rpow_mul]
    _ = ((2 : ℝ≥0∞)⁻¹) ^ ((m : ℝ) * namingDim O) := by rw [mul_comm]
    _ = (((2 : ℝ≥0∞)⁻¹) ^ (m : ℝ)) ^ namingDim O :=
      ENNReal.rpow_mul _ _ _
    _ = (((2 : ℝ≥0∞)⁻¹) ^ m) ^ namingDim O := by
      rw [ENNReal.rpow_natCast]
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ^ namingDim O := by
      rw [← hhalf, ← ENNReal.ofReal_pow (by norm_num)]

private theorem ediam_greenClass_range {O : Type*} [TopologicalSpace O] [DiscreteTopology O]
    [Nontrivial O] (m : ℕ) (t : ℕ → O) :
    Metric.ediam (greenClass (Finset.range m) t) = ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
  calc
    Metric.ediam (greenClass (Finset.range m) t) =
        ENNReal.ofReal (Metric.ediam (greenClass (Finset.range m) t)).toReal :=
      (ENNReal.ofReal_toReal
        (BoundedSpace.bounded_univ.subset (Set.subset_univ _)).ediam_ne_top).symm
    _ = ENNReal.ofReal (Metric.diam (greenClass (Finset.range m) t)) := rfl
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
      rw [green_class_diameter, D5.S0.Naming.FirstHoleBound.firstHole_range]

/-- The uniform string measure is bounded by critical powers of PiNat extended diameter. -/
theorem stringMeasure_le_ediam_rpow {O : Type*} [Fintype O] [Nonempty O] [Nontrivial O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [TopologicalSpace O]
    [DiscreteTopology O] (s : Set (ℕ → O)) :
    stringMeasure O s ≤ Metric.ediam s ^ namingDim O := by
  classical
  by_cases hs : s.Subsingleton
  · rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hsubset : s ⊆ {x} := fun y hy => by simpa using hs hy hx
    have hbound (m : ℕ) :
        stringMeasure O {x} ≤ ((Fintype.card O : ℝ≥0∞))⁻¹ ^ m := by
      calc
        stringMeasure O {x} ≤ stringMeasure O (greenClass (Finset.range m) x) :=
          measure_mono (by simp [greenClass])
        _ = ((Fintype.card O : ℝ≥0∞))⁻¹ ^ m := by
          simpa using greenClass_measure (O := O) (Finset.range m) x
    have htend : Tendsto (fun m : ℕ => ((Fintype.card O : ℝ≥0∞))⁻¹ ^ m) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (ENNReal.inv_lt_one.2 (by exact_mod_cast Fintype.one_lt_card (α := O)))
    have hsingle : stringMeasure O {x} = 0 :=
      nonpos_iff_eq_zero.mp (ge_of_tendsto' htend hbound)
    rw [nonpos_iff_eq_zero.mp ((measure_mono hsubset).trans_eq hsingle)]
    exact bot_le
  · have hex : ∃ i : ℕ, ∃ x ∈ s, ∃ y ∈ s, x i ≠ y i := by
      obtain ⟨x, hx, y, hy, hne⟩ := Set.not_subsingleton_iff.mp hs
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact ⟨i, x, hx, y, hy, hi⟩
    let m := Nat.find hex
    obtain ⟨x, hx, y, hy, hxy⟩ := Nat.find_spec hex
    have hagree {i : ℕ} (hi : i < m) {z w : ℕ → O} (hz : z ∈ s) (hw : w ∈ s) :
        z i = w i := by
      by_contra hzw
      exact Nat.find_min hex hi ⟨z, hz, w, hw, hzw⟩
    have hsubset : s ⊆ greenClass (Finset.range m) x := by
      intro z hz
      rw [mem_greenClass_iff]
      intro i hi
      exact hagree (Finset.mem_range.mp hi) hz hx
    have hne : x ≠ y := fun h => hxy (congrFun h m)
    have hfirst : PiNat.firstDiff x y = m := by
      apply le_antisymm
      · rw [PiNat.firstDiff_def, dif_pos hne]
        exact Nat.find_le hxy
      · by_contra hle
        exact PiNat.apply_firstDiff_ne hne (hagree (Nat.lt_of_not_ge hle) hx hy)
    have hdiam : (1 / 2 : ℝ) ^ m ≤ Metric.diam s := by
      calc
        (1 / 2 : ℝ) ^ m = dist x y := by rw [PiNat.dist_eq_of_ne hne, hfirst]
        _ ≤ Metric.diam s :=
          Metric.dist_le_diam_of_mem (Bornology.IsBounded.all _) hx hy
    have hediam : ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ≤ Metric.ediam s := by
      calc
        ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ≤ ENNReal.ofReal (Metric.diam s) :=
          ENNReal.ofReal_le_ofReal hdiam
        _ = Metric.ediam s := by
          exact ENNReal.ofReal_toReal
            (BoundedSpace.bounded_univ.subset (Set.subset_univ _)).ediam_ne_top
    calc
      stringMeasure O s ≤ stringMeasure O (greenClass (Finset.range m) x) :=
        measure_mono hsubset
      _ = ((Fintype.card O : ℝ≥0∞))⁻¹ ^ m := by
        simpa using greenClass_measure (O := O) (Finset.range m) x
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ m) ^ namingDim O :=
        inv_card_pow_eq_half_pow_rpow m
      _ ≤ Metric.ediam s ^ namingDim O :=
        ENNReal.rpow_le_rpow hediam namingDim_nonneg

/-- At the critical exponent, Hausdorff measure is the uniform string measure. -/
theorem hausdorffMeasure_eq_stringMeasure {O : Type*} [Fintype O] [Nonempty O]
    [Nontrivial O] [MeasurableSpace O] [MeasurableSingletonClass O] [TopologicalSpace O]
    [DiscreteTopology O] :
    (μH[namingDim O] : Measure (ℕ → O)) = stringMeasure O := by
  classical
  have hlower : stringMeasure O ≤ (μH[namingDim O] : Measure (ℕ → O)) :=
    Measure.le_hausdorffMeasure (namingDim O) (stringMeasure O) 1 zero_lt_one fun s _ =>
      stringMeasure_le_ediam_rpow s
  let extension (m : ℕ) (u : Fin m → O) : ℕ → O :=
    Fin.val.extend u (Classical.choice inferInstance)
  let cylinder (m : ℕ) (u : Fin m → O) : Set (ℕ → O) :=
    greenClass (Finset.range m) (extension m u)
  have hr : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) atTop (𝓝 0) := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    have hfun : (fun m : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) =
        fun m : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ m := by
      funext m
      rw [ENNReal.ofReal_pow (by norm_num), hhalf]
    rw [hfun]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (ENNReal.inv_lt_one.2 (by norm_num : (1 : ℝ≥0∞) < 2))
  have hdiam : ∀ᶠ m in atTop, ∀ u, Metric.ediam (cylinder m u) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
    filter_upwards [] with m u
    exact (ediam_greenClass_range m (extension m u)).le
  have hcover : ∀ᶠ m in atTop,
      (Set.univ : Set (ℕ → O)) ⊆ ⋃ u : Fin m → O, cylinder m u := by
    filter_upwards [] with m x hx
    rw [Set.mem_iUnion]
    refine ⟨fun i => x i, ?_⟩
    rw [mem_greenClass_iff]
    intro i hi
    simpa [extension] using
      (Fin.val_injective.extend_apply (fun j : Fin m => x j)
        (Classical.choice (inferInstance : Nonempty (ℕ → O)))
        ⟨i, Finset.mem_range.mp hi⟩).symm
  have hupper : (μH[namingDim O] : Measure (ℕ → O)) Set.univ ≤ 1 := by
    refine (Measure.hausdorffMeasure_le_liminf_sum (namingDim O) Set.univ
      (fun m : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) hr cylinder hdiam hcover).trans_eq ?_
    have hn0 : (Fintype.card O : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hn_top : (Fintype.card O : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    have hsum (m : ℕ) :
        ∑ _ : Fin m → O, ((Fintype.card O : ℝ≥0∞))⁻¹ ^ m = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_pow, ENNReal.mul_inv_cancel hn0 hn_top, one_pow]
    simp_rw [cylinder, ediam_greenClass_range, ← inv_card_pow_eq_half_pow_rpow, hsum]
    exact liminf_const (f := atTop) (1 : ℝ≥0∞)
  have hprob : (μH[namingDim O] : Measure (ℕ → O)) Set.univ = 1 :=
    le_antisymm hupper (by simpa using hlower Set.univ)
  letI : IsProbabilityMeasure (μH[namingDim O] : Measure (ℕ → O)) := ⟨hprob⟩
  exact (Measure.eq_of_le_of_isProbabilityMeasure hlower).symm

/-- The full naming space has Hausdorff dimension `namingDim O`. -/
theorem dimH_univ_eq_namingDim {O : Type*} [Fintype O] [Nonempty O] [Nontrivial O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [TopologicalSpace O]
    [DiscreteTopology O] :
    dimH (Set.univ : Set (ℕ → O)) = ENNReal.ofReal (namingDim O) := by
  have hd := namingDim_nonneg (O := O)
  have hmeasure : μH[(namingDim O).toNNReal] (Set.univ : Set (ℕ → O)) = 1 := by
    rw [Real.coe_toNNReal _ hd, hausdorffMeasure_eq_stringMeasure]
    simp
  change dimH (Set.univ : Set (ℕ → O)) = ((namingDim O).toNNReal : ℝ≥0∞)
  exact dimH_of_hausdorffMeasure_ne_zero_ne_top (d := (namingDim O).toNNReal)
    (s := (Set.univ : Set (ℕ → O))) (by rw [hmeasure]; exact one_ne_zero)
    (by rw [hmeasure]; exact ENNReal.one_ne_top)

/-- Every finite-support green class has the full naming-space Hausdorff dimension. -/
theorem dimH_greenClass_eq_namingDim {O : Type*} [Fintype O] [Nonempty O] [Nontrivial O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [TopologicalSpace O]
    [DiscreteTopology O] (S : Finset ℕ) (t : ℕ → O) :
    dimH (greenClass S t) = ENNReal.ofReal (namingDim O) := by
  have hd := namingDim_nonneg (O := O)
  have hmeasure : μH[(namingDim O).toNNReal] (greenClass S t) =
      stringMeasure O (greenClass S t) := by
    rw [Real.coe_toNNReal _ hd, hausdorffMeasure_eq_stringMeasure]
  change dimH (greenClass S t) = ((namingDim O).toNNReal : ℝ≥0∞)
  exact dimH_of_hausdorffMeasure_ne_zero_ne_top (d := (namingDim O).toNNReal)
    (s := greenClass S t) (by rw [hmeasure]; exact (greenClass_measure_pos S t).ne')
    (by rw [hmeasure]; exact measure_ne_top _ _)

end

end D5.S0.Asymptotics.MetricGeometry.GreenClassHausdorffDimension
