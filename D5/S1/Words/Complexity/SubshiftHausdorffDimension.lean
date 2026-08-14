/- GID: D5/S1/Words/Complexity/SubshiftHausdorffDimension
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/SubshiftHausdorffDimension
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Polynomial factor complexity forces the prefix-language subshift, including the golden subshift, to have Hausdorff dimension zero. Closedness, orbit-closure identification, uncountability, and perfectness are not covered. -/

import D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter
import D5.S1.Words.Complexity.MorseHedlund
import D5.S1.Words.GoldenFactorComplexity
import Mathlib

namespace D5.S1.Words.Complexity.SubshiftHausdorffDimension

open D5.S0.Asymptotics.MetricGeometry.GreenClassDiameter
open D5.S0.Naming.GreenClassMeasure
open MeasureTheory Measure Filter
open scoped ENNReal Topology NNReal

noncomputable section

attribute [local instance] PiNat.metricSpace PiNat.boundedSpace Pi.borelSpace

variable {A : Type*} [Fintype A] [Nonempty A] [Nontrivial A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [TopologicalSpace A] [DiscreteTopology A]

/-- Infinite words whose every prefix occurs as a factor of `x`. -/
def wordSubshift (x : ℕ → A) : Set (ℕ → A) :=
  {y | ∀ n : ℕ, (fun k : Fin n => y k.val) ∈ wordFactorSet x n}

omit [Nonempty A] [Nontrivial A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [TopologicalSpace A] [DiscreteTopology A] in
/-- The base word belongs to its prefix-language subshift. -/
theorem self_mem_wordSubshift (x : ℕ → A) : x ∈ wordSubshift x := by
  intro n
  exact mem_wordFactorSet.mpr ⟨0, by funext k; simp [wordFactor]⟩

omit [Nonempty A] [Nontrivial A] [MeasurableSpace A] [MeasurableSingletonClass A]
  [TopologicalSpace A] [DiscreteTopology A] in
/-- The prefix-language subshift is invariant under the one-step shift. -/
theorem wordSubshift_shift_invariant (x : ℕ → A) {y : ℕ → A} (hy : y ∈ wordSubshift x) :
    (fun j => y (j + 1)) ∈ wordSubshift x := by
  intro n
  obtain ⟨i, hi⟩ := mem_wordFactorSet.mp (hy (n + 1))
  refine mem_wordFactorSet.mpr ⟨i + 1, ?_⟩
  funext k
  have := congrFun hi k.succ
  simp only [wordFactor, Fin.val_succ] at this ⊢
  rw [this]
  congr 1
  omega

private def extend (n : ℕ) (u : Fin n → A) : ℕ → A :=
  Fin.val.extend u (Classical.choice inferInstance)

private def cyl (n : ℕ) (u : Fin n → A) : Set (ℕ → A) :=
  greenClass (Finset.range n) (extend n u)

private abbrev Idx (x : ℕ → A) (n : ℕ) :=
  {u : Fin n → A // u ∈ wordFactorSet x n}

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
private theorem ediam_cyl_le (n : ℕ) (u : Fin n → A) :
    Metric.ediam (cyl n u) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  have h : Metric.diam (cyl n u) = (1 / 2 : ℝ) ^ n := by
    rw [cyl, green_class_diameter, D5.S0.Naming.FirstHoleBound.firstHole_range]
  calc
    Metric.ediam (cyl n u) = ENNReal.ofReal (Metric.diam (cyl n u)) :=
      (ENNReal.ofReal_toReal
        (BoundedSpace.bounded_univ.subset (Set.subset_univ _)).ediam_ne_top).symm
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by rw [h]

omit [Nonempty A] [Nontrivial A] in
private theorem dimH_eq_zero_of (s : Set (ℕ → A))
    (h : ∀ d : ℝ≥0, 0 < d → μH[(d : ℝ)] s = 0) : dimH s = 0 := by
  refine le_antisymm (dimH_le fun d' hd' => ?_) bot_le
  by_cases h0 : d' = 0
  · simp [h0]
  · exact absurd hd' (by rw [h d' (pos_iff_ne_zero.mpr h0)]; exact ENNReal.zero_ne_top)

private theorem real_limit (C k : ℕ) (d : ℝ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => (C : ℝ) * (((n : ℝ) + 1) ^ k * (((1 / 2 : ℝ) ^ d)) ^ n))
      atTop (𝓝 0) := by
  set r : ℝ := (1 / 2 : ℝ) ^ d with hrdef
  have hr0 : (0 : ℝ) ≤ r := Real.rpow_nonneg (by norm_num) d
  have hrpos : (0 : ℝ) < r := Real.rpow_pos_of_pos (by norm_num) d
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hd
  have hshift : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ (n + 1))
      atTop (𝓝 0) := by
    have h :=
      (tendsto_pow_const_mul_const_pow_of_lt_one k hr0 hr1).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp [Function.comp]
  have hmul := hshift.const_mul ((C : ℝ) * r⁻¹)
  rw [mul_zero] at hmul
  refine hmul.congr fun n => ?_
  rw [pow_succ]
  field_simp

/-- Polynomial factor complexity makes every positive-dimensional Hausdorff measure vanish. -/
theorem hausdorffMeasure_wordSubshift_eq_zero (x : ℕ → A) (C k : ℕ)
    (hC : ∀ n, (wordFactorSet x n).card ≤ C * (n + 1) ^ k) {d : ℝ} (hd : 0 < d) :
    μH[d] (wordSubshift x) = 0 := by
  have hcover : μH[d] (wordSubshift x) ≤
      liminf (fun n : ℕ => ∑ i : Idx x n, Metric.ediam (cyl n i.1) ^ d) atTop := by
    refine Measure.hausdorffMeasure_le_liminf_sum (ι := fun n : ℕ => Idx x n) d
      (wordSubshift x) (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ?_
      (fun n i => cyl n i.1) ?_ ?_
    · have hfun : (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) =
          fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ n := by
        funext n
        rw [ENNReal.ofReal_pow (by norm_num)]
        congr 1
        rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      rw [hfun]
      exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (ENNReal.inv_lt_one.2 (by norm_num : (1 : ℝ≥0∞) < 2))
    · filter_upwards [] with n i using ediam_cyl_le n i.1
    · filter_upwards [] with n y hy
      rw [Set.mem_iUnion]
      refine ⟨⟨fun j : Fin n => y j.val, hy n⟩, ?_⟩
      simp only [cyl, greenClass, Set.mem_pi, Finset.mem_coe, Finset.mem_range,
        Set.mem_singleton_iff]
      intro i hi
      simpa [extend] using
        (Fin.val_injective.extend_apply (fun j : Fin n => y j.val)
          (Classical.choice (inferInstance : Nonempty (ℕ → A))) ⟨i, hi⟩).symm
  have hterm : ∀ n : ℕ, (∑ i : Idx x n, Metric.ediam (cyl n i.1) ^ d) ≤
      ENNReal.ofReal
        ((C : ℝ) * (((n : ℝ) + 1) ^ k * (((1 / 2 : ℝ) ^ d)) ^ n)) := by
    intro n
    have hsum : (∑ _i : Idx x n, (ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ^ d) =
        (Fintype.card (Idx x n)) • ((ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ^ d) := by
      rw [Finset.sum_const, Finset.card_univ]
    have hb : (∑ i : Idx x n, Metric.ediam (cyl n i.1) ^ d) ≤
        (Fintype.card (Idx x n)) • ((ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) ^ d) := by
      rw [← hsum]
      exact Finset.sum_le_sum fun i _ =>
        ENNReal.rpow_le_rpow (ediam_cyl_le n i.1) hd.le
    refine hb.trans ?_
    rw [nsmul_eq_mul, ENNReal.ofReal_rpow_of_pos (by positivity)]
    have hcard : (Fintype.card (Idx x n) : ℝ≥0∞) ≤
        ENNReal.ofReal ((C : ℝ) * ((n : ℝ) + 1) ^ k) := by
      rw [Fintype.card_coe]
      calc
        ((wordFactorSet x n).card : ℝ≥0∞) ≤ ((C * (n + 1) ^ k : ℕ) : ℝ≥0∞) := by
          exact_mod_cast hC n
        _ = ENNReal.ofReal ((C : ℝ) * ((n : ℝ) + 1) ^ k) := by
          rw [← ENNReal.ofReal_natCast]
          congr 1
          push_cast
          ring
    calc
      (Fintype.card (Idx x n) : ℝ≥0∞) * ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ d) ≤
          ENNReal.ofReal ((C : ℝ) * ((n : ℝ) + 1) ^ k) *
            ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ d) := mul_le_mul_left hcard _
      _ = ENNReal.ofReal
          ((C : ℝ) * (((n : ℝ) + 1) ^ k * (((1 / 2 : ℝ) ^ d)) ^ n)) := by
        have hrp : ((1 / 2 : ℝ) ^ n) ^ d = (((1 / 2 : ℝ)) ^ d) ^ n := by
          rw [← Real.rpow_natCast (1 / 2 : ℝ) n,
            ← Real.rpow_natCast (((1 / 2 : ℝ)) ^ d) n,
            ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hrp]
        ring
  refine le_antisymm (hcover.trans ?_) bot_le
  have hlim : Tendsto
      (fun n : ℕ => ENNReal.ofReal
        ((C : ℝ) * (((n : ℝ) + 1) ^ k * (((1 / 2 : ℝ) ^ d)) ^ n)))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp (real_limit C k d hd)
  calc
    liminf (fun n : ℕ => ∑ i : Idx x n, Metric.ediam (cyl n i.1) ^ d) atTop ≤
        liminf (fun n : ℕ => ENNReal.ofReal
          ((C : ℝ) * (((n : ℝ) + 1) ^ k * (((1 / 2 : ℝ) ^ d)) ^ n))) atTop :=
      liminf_le_liminf (Eventually.of_forall hterm)
    _ = 0 := hlim.liminf_eq

/-- A prefix-language subshift of polynomial factor complexity has Hausdorff dimension zero. -/
theorem dimH_wordSubshift_eq_zero (x : ℕ → A) (C k : ℕ)
    (hC : ∀ n, (wordFactorSet x n).card ≤ C * (n + 1) ^ k) :
    dimH (wordSubshift x) = 0 := by
  apply dimH_eq_zero_of
  intro d hd
  exact hausdorffMeasure_wordSubshift_eq_zero x C k hC hd

private theorem golden_wordFactorSet_card (n : ℕ) :
    (wordFactorSet D5.S1.Words.goldenWord n).card =
      (D5.S1.Words.goldenFactorSet n).card := by
  classical
  have himg : D5.S1.Words.goldenFactorSet n =
      (wordFactorSet D5.S1.Words.goldenWord n).image List.ofFn := by
    ext w
    simp only [Finset.mem_image, D5.S1.Words.mem_goldenFactorSet, mem_wordFactorSet]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨wordFactor D5.S1.Words.goldenWord n i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [himg, Finset.card_image_of_injective _ List.ofFn_injective]

/-- The golden subshift has Hausdorff dimension zero. -/
theorem dimH_goldenSubshift_eq_zero :
    dimH (wordSubshift D5.S1.Words.goldenWord) = 0 := by
  apply dimH_wordSubshift_eq_zero D5.S1.Words.goldenWord 1 1
  intro n
  have hcard : (wordFactorSet D5.S1.Words.goldenWord n).card = n + 1 := by
    rw [golden_wordFactorSet_card, D5.S1.Words.golden_factor_complexity]
  rw [hcard]
  ring_nf
  omega

#print axioms hausdorffMeasure_wordSubshift_eq_zero
#print axioms dimH_wordSubshift_eq_zero
#print axioms dimH_goldenSubshift_eq_zero

end

end D5.S1.Words.Complexity.SubshiftHausdorffDimension
