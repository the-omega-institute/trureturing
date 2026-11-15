/- GID: D5/S3/Estimation/TimeArrow/CategoricalProductPoisson
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/CategoricalProductPoisson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent categorical count vectors admit a uniform full product Poisson comparison. -/

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Tactic

/-! A common submeasure compares the complete independent categorical count law with
independent Poisson coordinates. Time aggregation preserves the full product law. -/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
variable {J : Type*} [Fintype J] [DecidableEq J]
/-- One occurrence of mark j as a complete count vector. -/
def unitMark (j : J) : J → ℕ := Pi.single j 1

/-- A single categorical increment, with remaining mass at the zero vector. -/
def categoricalIncrement (a : J → ℝ≥0) : Measure (J → ℕ) :=
  ENNReal.ofReal (1 - ∑ j, (a j : ℝ)) • Measure.dirac 0 +
    ∑ j, (a j : ℝ≥0∞) • Measure.dirac (unitMark j)

private def common (a : J → ℝ≥0) : Measure (J → ℕ) :=
  ENNReal.ofReal (1 - ∑ j, (a j : ℝ)) • Measure.dirac 0 +
    ∑ j, ENNReal.ofReal (Real.exp (-∑ i, (a i : ℝ)) * a j) • Measure.dirac (unitMark j)

private theorem poisson_zero (a : J → ℝ≥0) :
    (Measure.pi (fun j => poissonMeasure (a j))).real {0} = Real.exp (-∑ j, (a j : ℝ)) := by
  have hp (n : J → ℕ) :
      (Measure.pi (fun i => poissonMeasure (a i))).real {n} =
        ∏ i, (Real.exp (-(a i : ℝ)) * (a i : ℝ) ^ n i / (n i).factorial) := by
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    exact prod_congr rfl fun i _ => poissonMeasure_real_singleton (a i) (n i)
  rw [hp]
  simp only [Pi.zero_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  rw [← Real.exp_sum]
  congr 1
  simp

private theorem poisson_atom (a : J → ℝ≥0) (j : J) :
    (Measure.pi (fun i => poissonMeasure (a i))).real {unitMark j} =
      Real.exp (-∑ i, (a i : ℝ)) * a j := by
  have hp (n : J → ℕ) :
      (Measure.pi (fun i => poissonMeasure (a i))).real {n} =
        ∏ i, (Real.exp (-(a i : ℝ)) * (a i : ℝ) ^ n i / (n i).factorial) := by
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    exact prod_congr rfl fun i _ => poissonMeasure_real_singleton (a i) (n i)
  rw [hp]
  have he (i : J) : (a i : ℝ) ^ unitMark j i / (unitMark j i).factorial =
      if i = j then (a j : ℝ) else 1 := by
    by_cases h : i = j
    · subst i; simp [unitMark]
    · simp [unitMark, h]
  simp_rw [mul_div_assoc, he]
  rw [prod_mul_distrib, ← Real.exp_sum]
  simp

private theorem atom_ne_zero (j : J) : unitMark j ≠ 0 := by
  intro h
  have := congrFun h j
  simpa [unitMark] using this

private theorem atom_injective : Function.Injective (unitMark (J := J)) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [unitMark, Ne.symm hij] at this

private theorem common_le_cat (a : J → ℝ≥0) : common a ≤ categoricalIncrement a := by
  apply Measure.le_iff.mpr
  intro E hE
  simp only [common, categoricalIncrement, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have h : Real.exp (-∑ i, (a i : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sum_nonneg fun i _ => (a i).coe_nonneg))
  simpa using mul_le_mul_of_nonneg_right h (a j).coe_nonneg

private theorem common_le_poisson (a : J → ℝ≥0) :
    common a ≤ Measure.pi (fun i => poissonMeasure (a i)) := by
  have hp (n : J → ℕ) : common a {n} ≤ (Measure.pi (fun i => poissonMeasure (a i))) {n} := by
    by_cases hn : n = 0
    · subst n
      have hz : common a {0} = ENNReal.ofReal (1 - ∑ j, (a j : ℝ)) := by
        simp [common, Measure.finsetSum_apply, atom_ne_zero]
      rw [hz]
      have hh := Real.add_one_le_exp (-∑ j, (a j : ℝ))
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def, poisson_zero]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · by_cases he : ∃ j, n = unitMark j
      · obtain ⟨j,rfl⟩ := he
        have hh : common a {unitMark j} = ENNReal.ofReal (Real.exp (-∑ i, (a i : ℝ)) * a j) := by
          simp [common, Measure.finsetSum_apply, Pi.single_apply, atom_ne_zero, atom_injective.eq_iff]
        rw [hh, ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def, poisson_atom]
      · have hz : common a {n} = 0 := by
          simp [common, Measure.finsetSum_apply, Ne.symm hn,
            fun j => Ne.symm (show n ≠ unitMark j from fun h => he ⟨j,h⟩)]
        rw [hz]
        exact bot_le
  apply Measure.le_iff.mpr
  intro E hE
  conv_lhs => rw [← (common a).sum_smul_dirac]
  conv_rhs => rw [← (Measure.pi (fun i => poissonMeasure (a i))).sum_smul_dirac]
  simp only [Measure.sum_apply _ hE, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum fun n => mul_le_mul_of_nonneg_right (hp n) (by positivity)


private theorem discrete_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (μ ν : Measure X) (h : ∀ x, μ {x} ≤ ν {x}) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro E hE
  conv_lhs => rw [← μ.sum_smul_dirac]
  conv_rhs => rw [← ν.sum_smul_dirac]
  simp only [Measure.sum_apply _ hE, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_le_tsum fun n => mul_le_mul_of_nonneg_right (h n) (by positivity)

private theorem pi_mono_discrete {I X : Type*} [Fintype I] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (μ ν : I → Measure X)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  apply discrete_le
  intro x
  simp only [Measure.pi_singleton]
  exact prod_le_prod' fun i _ => h i {x i}

private theorem cat_probability (a : J → ℝ≥0) (ha : ∑ j, (a j : ℝ) ≤ 1) :
    IsProbabilityMeasure (categoricalIncrement a) := by
  constructor
  simp only [categoricalIncrement, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  have hs : (∑ j, (a j : ℝ≥0∞)) = ENNReal.ofReal (∑ j, (a j : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (a j).coe_nonneg)]
    simp
  rw [hs, ← ENNReal.ofReal_add (sub_nonneg.mpr ha) (by positivity)]
  simp

/-- The vector sum map keeps every mark coordinate on the same increment history. -/
def aggregateCounts (s : ℕ) (x : Fin s → J → ℕ) : J → ℕ := fun j => ∑ t, x t j

/-- Law of the sum of s independent increments with common law μ. -/
def independentSumLaw (μ : Measure (J → ℕ)) (s : ℕ) : Measure (J → ℕ) :=
  (Measure.pi (fun _ : Fin s => μ)).map (aggregateCounts s)

private theorem sumLaw_mono (μ ν : Measure (J → ℕ)) [SigmaFinite μ] [SigmaFinite ν]
    (h : μ ≤ ν) (s : ℕ) : independentSumLaw μ s ≤ independentSumLaw ν s :=
  Measure.map_mono (pi_mono_discrete _ _ fun _ => h) (by fun_prop)

private theorem sumLaw_mass (μ : Measure (J → ℕ)) [SigmaFinite μ] (s : ℕ) :
    (independentSumLaw μ s).real Set.univ = (μ.real Set.univ) ^ s := by
  simp [independentSumLaw, measureReal_def, Measure.map_apply (by fun_prop : Measurable (aggregateCounts (J := J) s)),
    Measure.pi_univ, ENNReal.toReal_pow]

private theorem sumLaw_succ (μ : Measure (J → ℕ)) [SigmaFinite μ] (s : ℕ) :
    independentSumLaw μ (s+1) = μ ∗ independentSumLaw μ s := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (s+1) => J → ℕ) 0
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (s+1) => μ) 0).map_eq
  have ht : aggregateCounts (J := J) (s+1) =
      (fun p : (J → ℕ) × (Fin s → J → ℕ) => p.1 + aggregateCounts s p.2) ∘ e := by
    funext x j
    simp [aggregateCounts, e, MeasurableEquiv.piFinSuccAbove, Fin.sum_univ_succ, Fin.tail]
  rw [independentSumLaw, ht, ← Measure.map_map (by fun_prop) e.measurable, h]
  have hm := Measure.map_prod_map μ (Measure.pi (fun _ : Fin s => μ))
    measurable_id (show Measurable (aggregateCounts (J := J) s) by fun_prop)
  rw [Measure.map_id] at hm
  rw [Measure.conv, independentSumLaw, hm, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

private theorem poisson_product_add (a b : J → ℝ≥0) :
    (Measure.pi fun j => poissonMeasure (a j)) ∗ (Measure.pi fun j => poissonMeasure (b j)) =
      Measure.pi (fun j => poissonMeasure (a j + b j)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ J
  have h := (measurePreserving_arrowProdEquivProdArrow ℕ ℕ J
    (fun j => poissonMeasure (a j)) (fun j => poissonMeasure (b j))).map_eq
  rw [Measure.conv, ← h, Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun j => (poissonMeasure (a j)).prod (poissonMeasure (b j)))).map
    (fun x j => (x j).1 + (x j).2) = _
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (fun p : ℕ × ℕ => p.1 + p.2)).aemeasurable)]
  congr 1
  funext j
  exact poissonMeasure_conv_poissonMeasure (a j) (b j)

private theorem poisson_product_zero :
    (Measure.pi (fun _ : J => poissonMeasure 0)) = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  simp only [Measure.pi_singleton, poissonMeasure_singleton]
  by_cases hn : n = 0
  · subst n; simp
  · obtain ⟨j,hj⟩ : ∃ j, n j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (funext h)
    rw [prod_eq_zero (mem_univ j)]
    · simp [hn, Ne.symm hn]
    · simp [hj]

/-- Aggregating time preserves the whole independent product law. -/
private theorem poisson_product_sum (a : J → ℝ≥0) (s : ℕ) :
    independentSumLaw (Measure.pi fun j => poissonMeasure (a j)) s =
      Measure.pi (fun j => poissonMeasure (s * a j)) := by
  induction s with
  | zero =>
      rw [independentSumLaw, Measure.pi_of_empty (fun _ : Fin 0 => Measure.pi (fun j => poissonMeasure (a j)))
        (fun t => Fin.elim0 t), Measure.map_dirac' (by fun_prop : Measurable (aggregateCounts (J := J) 0))]
      have ht0 : aggregateCounts (J := J) 0 (fun t => Fin.elim0 t) = 0 := by
        funext j
        simp [aggregateCounts]
      rw [ht0]
      simpa only [Nat.cast_zero, zero_mul] using poisson_product_zero (J := J).symm
  | succ s ih =>
      rw [sumLaw_succ, ih, poisson_product_add]
      congr 1
      funext j
      congr 1
      push_cast
      ring

private theorem overlap_event {X : Type*} [MeasurableSpace X]
    (μ ν c : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : c ≤ μ) (hν : c ≤ ν) {E : Set X} (hE : MeasurableSet E) :
    |μ.real E - ν.real E| ≤ 1 - c.real Set.univ := by
  haveI : IsFiniteMeasure c := isFiniteMeasure_of_le μ hμ
  have h1 := ENNReal.toReal_mono (measure_ne_top μ E) (hμ E)
  have h2 := ENNReal.toReal_mono (measure_ne_top ν E) (hν E)
  have h3 := ENNReal.toReal_mono (measure_ne_top μ Eᶜ) (hμ Eᶜ)
  have h4 := ENNReal.toReal_mono (measure_ne_top ν Eᶜ) (hν Eᶜ)
  have hc := measureReal_add_measureReal_compl (μ := c) hE
  have hp := probReal_add_probReal_compl (μ := μ) hE
  have hq := probReal_add_probReal_compl (μ := ν) hE
  change c.real E ≤ μ.real E at h1
  change c.real E ≤ ν.real E at h2
  change c.real Eᶜ ≤ μ.real Eᶜ at h3
  change c.real Eᶜ ≤ ν.real Eᶜ at h4
  rw [abs_le]
  constructor <;> linarith

private theorem common_mass (a : J → ℝ≥0) (ha : ∑ j, (a j : ℝ) ≤ 1) :
    (common a).real Set.univ =
      1 - (∑ j, (a j : ℝ)) * (1 - Real.exp (-∑ j, (a j : ℝ))) := by
  haveI := cat_probability a ha
  haveI : IsFiniteMeasure (common a) := isFiniteMeasure_of_le (categoricalIncrement a) (common_le_cat a)
  simp only [common, measureReal_def, Measure.add_apply, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)), ENNReal.toReal_ofReal (sub_nonneg.mpr ha),
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.exp (-∑ i, (a i : ℝ)) * a _)]
  rw [← mul_sum]
  ring

/-- Uniform comparison with the full product Poisson law, without a count cutoff. -/
theorem categorical_product_poisson (a : J → ℝ≥0) (ha : ∑ j, (a j : ℝ) ≤ 1)
    (s : ℕ) (E : Set (J → ℕ)) :
    |(independentSumLaw (categoricalIncrement a) s).real E -
      (Measure.pi (fun j => poissonMeasure (s * a j))).real E| ≤
        s * (∑ j, (a j : ℝ)) ^ 2 := by
  haveI := cat_probability a ha
  haveI : IsFiniteMeasure (common a) := isFiniteMeasure_of_le (categoricalIncrement a) (common_le_cat a)
  haveI : IsProbabilityMeasure (independentSumLaw (categoricalIncrement a) s) := by
    dsimp [independentSumLaw]
    infer_instance
  haveI : IsProbabilityMeasure (independentSumLaw (Measure.pi fun j => poissonMeasure (a j)) s) := by
    dsimp [independentSumLaw]
    infer_instance
  let ρ : ℝ := ∑ j, (a j : ℝ)
  let d : ℝ := ρ * (1 - Real.exp (-ρ))
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hd : 0 ≤ d := mul_nonneg hρ (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hρ)))
  have hdρ : d ≤ ρ ^ 2 := by
    have hh := Real.add_one_le_exp (-ρ)
    dsimp [d]
    nlinarith
  have hmass : (common a).real Set.univ = 1 - d := common_mass a ha
  have hd1 : d ≤ 1 := by
    have hc : 0 ≤ (common a).real Set.univ := measureReal_nonneg
    rw [hmass] at hc
    linarith
  have hb (n : ℕ) : 1 - (1-d) ^ n ≤ n * d := by
    have h := one_add_mul_le_pow (a := -d) (by linarith : -2 ≤ -d) n
    simp only [mul_neg, ← sub_eq_add_neg] at h
    linarith
  have h := overlap_event (independentSumLaw (categoricalIncrement a) s)
    (independentSumLaw (Measure.pi fun j => poissonMeasure (a j)) s) (independentSumLaw (common a) s)
    (sumLaw_mono _ _ (common_le_cat a) s)
    (sumLaw_mono _ _ (common_le_poisson a) s)
    E.to_countable.measurableSet
  rw [poisson_product_sum, sumLaw_mass, hmass] at h
  exact h.trans ((hb s).trans (mul_le_mul_of_nonneg_left hdρ (by positivity)))

end D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
