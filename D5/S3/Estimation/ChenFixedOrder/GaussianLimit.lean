/- GID: D5/S3/Estimation/ChenFixedOrder/GaussianLimit
   generality: I
   mirror-B: D5/B/S3/Estimation/ChenFixedOrder/GaussianLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Gaussian limit for the balanced-sign estimator under uniform fixed-size sampling. -/

import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.InfinitePi
import D5.S3.Analytic.Probability.ChenFixedOrderSampling
import D5.S3.Analytic.Probability.MomentPerturbation

/-! The Gaussian limit of the centered estimator for the balanced finite populations in
the fixed-order sampling construction. -/

open ChenFixedOrderSampling MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Finset

namespace D5.S3.Estimation.ChenFixedOrder.GaussianLimit

open D5.S3.Analytic.Probability.MomentPerturbation (standardGaussian)

noncomputable section

private def orderedEstimator (m : ℕ) (x : Draw m) : ℝ :=
  Real.sqrt (sampleSize m : ℝ) *
    ((∑ i, populationValue m (x i)) / (sampleSize m : ℝ) - populationMean m)

/-- The independent uniform draws of labels, with replacement. -/
private def drawMeasure (m : ℕ) : Measure (Draw m) :=
  uniformOn Set.univ

private instance (m : ℕ) : IsProbabilityMeasure (drawMeasure m) := by
  have h : 0 < stratumSize m := by positivity
  let : Nonempty (Fin (stratumSize m)) := ⟨⟨0, h⟩⟩
  unfold drawMeasure
  infer_instance

private theorem drawMeasure_eq_pi (m : ℕ) :
    drawMeasure m = Measure.pi (fun _ => uniformOn Set.univ) := by
  simpa [drawMeasure] using
    (uniformOn_pi (ι := Fin (sampleSize m)) (f := fun _ => (Set.univ : Set (Population m))))

private def withReplacementLaw (m : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map ⟨drawMeasure m, inferInstance⟩ (orderedEstimator m)

private def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

private def signLaw : Measure ℝ := bernoulliMeasure 1 (-1) half

private instance : IsProbabilityMeasure signLaw := by unfold signLaw; infer_instance

private def signProduct : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => signLaw)

private instance : IsProbabilityMeasure signProduct := by unfold signProduct; infer_instance

private def normalizedSum (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, x k

private theorem normalizedSum_clt :
    TendstoInDistribution normalizedSum atTop (id : ℝ → ℝ) (fun _ => signProduct)
      (gaussianReal 0 1) := by
  have hl (i : ℕ) : HasLaw (fun x : ℕ → ℝ => x i) signLaw signProduct :=
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  refine tendstoInDistribution_inv_sqrt_mul_sum HasLaw.id ?_ ?_ ?_ ?_
  · rw [(hl 0).integral_eq]
    norm_num [signLaw, integral_bernoulliMeasure, half]
  · change (∫ x, ((fun y : ℝ => y ^ 2) ∘ (fun ω : ℕ → ℝ => ω 0)) x ∂signProduct) = 1
    rw [(hl 0).integral_comp (by fun_prop)]
    norm_num [signLaw, integral_bernoulliMeasure, half]
  · exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  · intro i
    exact (hl i).identDistrib (hl 0)

/-- Both strata have the same number of labels, so a single uniform label has a fair sign. -/
private theorem map_populationValue (m : ℕ) :
    (uniformOn (Set.univ : Set (Population m))).map (populationValue m) = signLaw := by
  classical
  have emptyPreimage (s : Set ℝ) (hp : (1 : ℝ) ∉ s) (hn : (-1 : ℝ) ∉ s) :
      populationValue m ⁻¹' s = ∅ := by
    ext p
    by_cases h : p.1 = 0 <;> simp [populationValue, h, hp, hn]
  have univPreimage (s : Set ℝ) (hp : (1 : ℝ) ∈ s) (hn : (-1 : ℝ) ∈ s) :
      populationValue m ⁻¹' s = Set.univ := by
    ext p
    by_cases h : p.1 = 0 <;> simp [populationValue, h, hp, hn]
  have stratumMass (i : Fin 2) :
      uniformOn (Set.univ : Set (Population m)) {p | p.1 = i} =
        (unitInterval.toNNReal half : ℝ≥0∞) := by
    have he : ({p : Population m | p.1 = i} : Set (Population m)) =
        ↑(({i} : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin (stratumSize m)))) := by
      ext p
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_product, Finset.mem_singleton,
        Finset.mem_univ, and_true]
    rw [he, uniformOn_univ, Measure.count_apply_finset, Finset.card_product]
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin, one_mul,
      Fintype.card_prod, Nat.cast_mul, Nat.cast_ofNat]
    change (stratumSize m : ℝ≥0∞) / (2 * (stratumSize m : ℝ≥0∞)) = _
    have h : (stratumSize m : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (show stratumSize m ≠ 0 from pow_ne_zero 3 (sampleSize_pos m).ne')
    calc
      _ = (1 * (stratumSize m : ℝ≥0∞)) / (2 * (stratumSize m : ℝ≥0∞)) := by rw [one_mul]
      _ = 1 / 2 := ENNReal.mul_div_mul_right 1 2 h (ENNReal.natCast_ne_top _)
      _ = _ := ?_
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) ENNReal.coe_ne_top).mp
    change (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ)
    norm_num
  have half_symm : unitInterval.toNNReal (unitInterval.symm half) =
      unitInterval.toNNReal half := by
    ext
    norm_num [half, unitInterval.toNNReal, unitInterval.symm]
  let : Nonempty (Fin (stratumSize m)) :=
    ⟨⟨0, pow_pos (sampleSize_pos m) _⟩⟩
  unfold signLaw
  apply eq_bernoulliMeasure
  · intro s hs hp hn
    rw [Measure.map_apply (measurable_of_countable _) hs, univPreimage s hp hn]
    exact measure_univ
  · intro s hs hp hn
    rw [Measure.map_apply (measurable_of_countable _) hs, ← stratumMass 0]
    congr 1
    ext p
    by_cases h : p.1 = 0 <;> simp [populationValue, h, hp, hn]
  · intro s hs hp hn
    rw [Measure.map_apply (measurable_of_countable _) hs, half_symm, ← stratumMass 1]
    congr 1
    ext p
    have h : p.1 ≠ 0 ↔ p.1 = 1 := by
      generalize p.1 = i
      fin_cases i <;> decide
    by_cases hi : p.1 = 0
    · simp [populationValue, hi, hp]
    · simp [populationValue, hn, h.mp hi]
  · intro s hs hp hn
    rw [Measure.map_apply (measurable_of_countable _) hs, emptyPreimage s hp hn, measure_empty]

private theorem orderedEstimator_eq_normalized (m : ℕ) (x : Draw m) :
    orderedEstimator m x = (Real.sqrt (sampleSize m : ℝ))⁻¹ * ∑ i, populationValue m (x i) := by
  have hn : 0 < (sampleSize m : ℝ) := by exact_mod_cast sampleSize_pos m
  have hs := Real.sq_sqrt hn.le
  rw [orderedEstimator, populationMean_eq_zero, sub_zero]
  field_simp
  rw [hs, mul_comm]

private theorem map_orderedEstimator (m : ℕ) :
    (drawMeasure m).map (orderedEstimator m) = signProduct.map (normalizedSum (sampleSize m)) := by
  let n := sampleSize m
  let signs : Draw m → Fin n → ℝ := fun x i => populationValue m (x i)
  let e : Fin n ≃ ↥(Finset.range n) := (Finset.equivFinOfCardEq (Finset.card_range n)).symm
  let reindex : (Fin n → ℝ) ≃ᵐ (↥(Finset.range n) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
  let sumOnRange : (↥(Finset.range n) → ℝ) → ℝ :=
    fun y => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, y i
  have hsigns : (drawMeasure m).map signs = Measure.pi (fun _ : Fin n => signLaw) := by
    have (i : Fin n) :
        IsProbabilityMeasure
          ((uniformOn (Set.univ : Set (Population m))).map (populationValue m)) := by
      rw [map_populationValue]
      infer_instance
    rw [drawMeasure_eq_pi, Measure.pi_map_pi (fun _ => (measurable_of_countable _).aemeasurable)]
    simp only [map_populationValue, n]
  have hreindex : (Measure.pi (fun _ : Fin n => signLaw)).map reindex =
      Measure.pi (fun _ : ↥(Finset.range n) => signLaw) :=
    Measure.pi_map_piCongrLeft e (fun _ => signLaw)
  have hmeas : Measurable sumOnRange := by dsimp [sumOnRange]; fun_prop
  have hleft : orderedEstimator m = sumOnRange ∘ reindex ∘ signs := by
    funext x
    rw [orderedEstimator_eq_normalized]
    change _ = (Real.sqrt (n : ℝ))⁻¹ * ∑ i, reindex (signs x) i
    rw [← e.sum_comp (fun i => reindex (signs x) i)]
    simp only [reindex, MeasurableEquiv.piCongrLeft_apply_apply, signs, n]
  have hright : normalizedSum n = sumOnRange ∘ (Finset.range n).restrict := by
    funext x
    unfold normalizedSum sumOnRange
    rw [Function.comp_apply, ← Finset.sum_attach (Finset.range n) (fun k => x k)]
    rfl
  have hrestrict : Measurable ((Finset.range n).restrict : (ℕ → ℝ) → _) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  rw [hleft, ← Measure.map_map hmeas (reindex.measurable.comp (measurable_of_countable _)),
    ← Measure.map_map reindex.measurable (measurable_of_countable _), hsigns, hreindex,
    hright, ← Measure.map_map hmeas hrestrict,
    signProduct, Measure.infinitePi_map_restrict]

/-- The centered estimator from the independent uniform population labels converges weakly
to the standard Gaussian as the sample size grows through the prescribed squares. -/
private theorem withReplacement_tendsto :
    Tendsto withReplacementLaw atTop (𝓝 standardGaussian) := by
  have h := normalizedSum_clt.tendsto.comp sampleSize_tendsto
  rw [show (⟨(gaussianReal 0 1).map id, inferInstance⟩ : ProbabilityMeasure ℝ) =
      standardGaussian from ProbabilityMeasure.toMeasure_injective (Measure.map_id)] at h
  refine h.congr fun m => ProbabilityMeasure.toMeasure_injective ?_
  exact (map_orderedEstimator m).symm

private theorem measurableSet_distinct (m : ℕ) : MeasurableSet (distinct m) :=
  (distinct m).toFinite.measurableSet

private theorem populationCard_eq (m : ℕ) :
    Fintype.card (Population m) = 2 * sampleSize m ^ 3 := by
  change Fintype.card (Fin 2 × Fin (stratumSize m)) = _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

private theorem populationCard_pos (m : ℕ) : 0 < Fintype.card (Population m) := by
  rw [populationCard_eq]
  exact Nat.mul_pos (by decide) (pow_pos (sampleSize_pos m) 3)

/-- For two distinct positions, sum the equal-label cylinders over population labels. -/
private theorem pairCollision_le (m : ℕ) (i j : Fin (sampleSize m)) (hij : i ≠ j) :
    drawMeasure m {x | x i = x j} ≤ (Fintype.card (Population m) : ℝ≥0∞)⁻¹ := by
  let d : ℝ≥0∞ := Fintype.card (Population m)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (populationCard_pos m).ne'
  have hd' : d ≠ ∞ := ENNReal.natCast_ne_top _
  have : Nonempty (Fin (stratumSize m)) := ⟨⟨0, pow_pos (sampleSize_pos m) _⟩⟩
  let cylinder (p : Population m) : Set (Draw m) := {x | x i = p ∧ x j = p}
  have cover : {x : Draw m | x i = x j} ⊆ ⋃ p ∈ Finset.univ, cylinder p := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨x j, Finset.mem_univ _, hx, rfl⟩
  have hc (p : Population m) : drawMeasure m (cylinder p) = d⁻¹ * d⁻¹ := by
    have he : cylinder p =
        (↑({i, j} : Finset (Fin (sampleSize m))) : Set (Fin (sampleSize m))).pi
          (fun _ => ({p} : Set (Population m))) := by
      ext x
      simp [cylinder]
    rw [he, drawMeasure_eq_pi, Measure.pi_pi_finset, Finset.prod_pair hij]
    simp [uniformOn_univ, d]
  calc
    _ ≤ drawMeasure m (⋃ p ∈ Finset.univ, cylinder p) := measure_mono cover
    _ ≤ ∑ p, drawMeasure m (cylinder p) := measure_biUnion_finset_le _ _
    _ = d * (d⁻¹ * d⁻¹) := by simp [hc, d, nsmul_eq_mul]
    _ = d⁻¹ := ENNReal.mul_inv_cancel_left hd hd'

/-- The union bound over pairs gives a collision probability at most (1/(2n_m)). -/
private theorem collisionMass_le (m : ℕ) :
    (drawMeasure m).real (distinct m)ᶜ ≤ 1 / (2 * (sampleSize m : ℝ)) := by
  classical
  let n := sampleSize m
  let N := Fintype.card (Population m)
  let collision (ij : Fin n × Fin n) : Set (Draw m) :=
    {x | ij.1 ≠ ij.2 ∧ x ij.1 = x ij.2}
  have cover : (distinct m)ᶜ ⊆ ⋃ ij ∈ Finset.univ, collision ij := by
    intro x hx
    change ¬ Function.Injective x at hx
    unfold Function.Injective at hx
    push Not at hx
    obtain ⟨i, j, heq, hne⟩ := hx
    exact Set.mem_iUnion₂.mpr ⟨(i, j), Finset.mem_univ _, hne, heq⟩
  have hc (ij : Fin n × Fin n) : drawMeasure m (collision ij) ≤ (N : ℝ≥0∞)⁻¹ := by
    by_cases h : ij.1 = ij.2
    · simp [collision, h]
    · have hsubset : collision ij ⊆ {x | x ij.1 = x ij.2} := fun _ hx => hx.2
      exact (measure_mono hsubset).trans (pairCollision_le m ij.1 ij.2 h)
  have hbound : drawMeasure m (distinct m)ᶜ ≤ (n : ℝ≥0∞)^2 * (N : ℝ≥0∞)⁻¹ := calc
    _ ≤ drawMeasure m (⋃ ij ∈ Finset.univ, collision ij) := measure_mono cover
    _ ≤ ∑ ij, drawMeasure m (collision ij) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _ : Fin n × Fin n, (N : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum fun ij _ => hc ij
    _ = _ := by simp [Fintype.card_prod, nsmul_eq_mul, pow_two, ← Nat.cast_mul]
  have hN : N = 2 * n^3 := populationCard_eq m
  have hn : 0 < (n : ℝ) := by exact_mod_cast sampleSize_pos m
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top n))
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast (populationCard_pos m).ne'))) hbound
  calc
    _ ≤ (n : ℝ)^2 * (N : ℝ)⁻¹ := by
      simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
        ENNReal.toReal_natCast] using hreal
    _ = 1 / (2 * (n : ℝ)) := by
      rw [hN]
      push_cast
      field_simp

/-- The collision mass vanishes along the prescribed sampling sizes. -/
private theorem collisionMass_tendsto :
    Tendsto (fun m => (drawMeasure m).real (distinct m)ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) collisionMass_le
  have h : Tendsto (fun m => (sampleSize m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp sampleSize_tendsto
  simp_rw [one_div]
  change Tendsto ((fun r : ℝ => r⁻¹) ∘ (fun m => 2 * (sampleSize m : ℝ))) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp (h.const_mul_atTop (by norm_num : 0 < (2 : ℝ)))

private theorem distinctDraws_measure_ne_zero (m : ℕ) : drawMeasure m (distinct m) ≠ 0 := by
  intro hz
  have hc := measureReal_add_measureReal_compl (μ := drawMeasure m) (measurableSet_distinct m)
  have hone : (drawMeasure m).real (distinct m)ᶜ = 1 := by
    simpa [measureReal_def, hz] using hc
  have hn : 1 ≤ (sampleSize m : ℝ) := by exact_mod_cast sampleSize_pos m
  have hh := collisionMass_le m
  rw [hone, le_div_iff₀ (by positivity)] at hh
  linarith

private def distinctMeasure (m : ℕ) : Measure (Draw m) :=
  cond (drawMeasure m) (distinct m)

private instance (m : ℕ) : IsProbabilityMeasure (distinctMeasure m) :=
  cond_isProbabilityMeasure (distinctDraws_measure_ne_zero m)

private def distinctLaw (m : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map ⟨distinctMeasure m, inferInstance⟩ (orderedEstimator m)

private theorem conditional_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {D : Set Ω}
    (hD : MeasurableSet D) (hq : μ D ≠ 0)
    (f : Ω → ℝ) (hf : Integrable f μ) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x, f x ∂cond μ D) - ∫ x, f x ∂μ‖ ≤ 2 * C * μ.real Dᶜ := by
  let : IsProbabilityMeasure (cond μ D) := cond_isProbabilityMeasure hq
  have hs : μ D • cond μ D = μ.restrict D := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hq (measure_ne_top μ D), one_smul]
  have hi : μ.real D * (∫ x, f x ∂cond μ D) = ∫ x in D, f x ∂μ := by
    simpa only [hs, measureReal_def, smul_eq_mul] using
      (integral_smul_measure (μ := cond μ D) f (μ D)).symm
  have hsplit := integral_add_compl hD hf
  have hp : μ.real D + μ.real Dᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hD
  have hrewrite : (∫ x, f x ∂cond μ D) - (∫ x, f x ∂μ) =
    μ.real Dᶜ * (∫ x, f x ∂cond μ D) - ∫ x in Dᶜ, f x ∂μ := by
    rw [← hsplit, ← hi, show μ.real Dᶜ = 1 - μ.real D by linarith]
    ring
  have h1 : ‖∫ x, f x ∂cond μ D‖ ≤ C := by
    simpa using
      (norm_integral_le_of_norm_le_const (μ := cond μ D) (Eventually.of_forall hC))
  have h2 : ‖∫ x in Dᶜ, f x ∂μ‖ ≤ C * μ.real Dᶜ :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top μ _) (fun x _ => hC x)
  rw [hrewrite]
  calc
    _ ≤ ‖μ.real Dᶜ * (∫ x, f x ∂cond μ D)‖ + ‖∫ x in Dᶜ, f x ∂μ‖ :=
      norm_sub_le _ _
    _ ≤ μ.real Dᶜ * C + C * μ.real Dᶜ := by
      have hnonneg : 0 ≤ μ.real Dᶜ := ENNReal.toReal_nonneg
      rw [norm_mul, Real.norm_of_nonneg hnonneg]
      exact add_le_add (mul_le_mul_of_nonneg_left h1 hnonneg) h2
    _ = 2 * C * μ.real Dᶜ := by ring

/-- Conditioning on distinct labels changes any bounded measurable test by at most twice its
uniform bound times the collision probability. -/
private theorem distinctLaw_test_bound (m : ℕ) (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x, f x ∂(distinctLaw m : Measure ℝ)) - ∫ x, f x ∂(withReplacementLaw m : Measure ℝ)‖ ≤
      2 * C * (drawMeasure m).real (distinct m)ᶜ := by
  have hm := measurable_of_countable (orderedEstimator m)
  have hfi : Integrable (f ∘ orderedEstimator m) (drawMeasure m) :=
    Integrable.of_bound (hf.comp hm).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (orderedEstimator m x))
  change ‖(∫ x, f x ∂(distinctMeasure m).map (orderedEstimator m)) -
    ∫ x, f x ∂(drawMeasure m).map (orderedEstimator m)‖ ≤ _
  simp only [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact conditional_bounded _ (measurableSet_distinct m) (distinctDraws_measure_ne_zero m)
    _ hfi C (fun x => hC (orderedEstimator m x))

/-- The estimator law conditioned on all labels being distinct has the same Gaussian limit. -/
private theorem distinctLaw_tendsto : Tendsto distinctLaw atTop (𝓝 standardGaussian) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hwr := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp withReplacement_tendsto f
  have hdiff :
      Tendsto (fun m => (∫ x, f x ∂(distinctLaw m : Measure ℝ)) -
        ∫ x, f x ∂(withReplacementLaw m : Measure ℝ)) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [dist_zero_right]
    refine squeeze_zero (g := fun m => 2 * ‖f‖ * (drawMeasure m).real (distinct m)ᶜ)
      (fun _ => norm_nonneg _) (fun m => ?_) ?_
    · exact distinctLaw_test_bound m f f.continuous.measurable ‖f‖ f.norm_coe_le_norm
    · simpa only [mul_zero] using collisionMass_tendsto.const_mul (2 * ‖f‖)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hwr

private theorem estimator_eraseOrder (m : ℕ) {x : Draw m} (hx : x ∈ distinct m) :
    estimator m (eraseOrder m x) = orderedEstimator m x := by
  unfold estimator orderedEstimator
  rw [eraseOrder_val m x hx, Finset.sum_image (show Function.Injective x from hx).injOn]

/-- The centered estimator under uniform sampling of fixed-size subsets converges weakly
to the standard Gaussian. -/
theorem uniformSampleLaw_tendsto :
    Tendsto (fun m => (uniformSampleMeasure m).map (estimator m)) atTop (𝓝 standardGaussian) := by
  refine distinctLaw_tendsto.congr fun m => ProbabilityMeasure.toMeasure_injective ?_
  change (distinctMeasure m).map (orderedEstimator m) =
    (uniformOn (Set.univ : Set (Sample m))).map (estimator m)
  rw [← map_eraseOrder_cond_uniform m,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  apply Measure.map_congr
  exact (ae_cond_mem (μ := drawMeasure m) (measurableSet_distinct m)).mono
    fun _ hx => (estimator_eraseOrder m hx).symm

end

end D5.S3.Estimation.ChenFixedOrder.GaussianLimit
