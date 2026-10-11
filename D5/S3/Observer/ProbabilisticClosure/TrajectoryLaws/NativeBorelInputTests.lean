/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded Borel input tests recover the complete normalized residual measures. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelTVTopology
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelInputTests
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open FourthSegmentStoppedLaw NativeFullResidual NativeBorelCommonFlow NativeBorelRepresentation
open NativeConditionalControl.Tail NativeBorelTVTopology

instance lawKernel_markov (s : ActivePhase) : IsMarkovKernel (lawKernel s) :=
  ⟨fun D => inferInstanceAs (IsProbabilityMeasure (law D))⟩

def discrepancy {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (R S : X → Measure Y) (t : Y) (x : X) : ℝ :=
  (R x).real {t} - (S x).real {t}

def InputTests {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (R S : X → Measure Y) : Prop :=
  ∀ (t : Y) (φ : X → ℝ), Measurable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
    ∫ x, φ x * discrepancy R S t x ∂ν = 0

private theorem probability_input_tests {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Countable Y] [MeasurableSingletonClass Y]
    (ν : Measure X) [IsFiniteMeasure ν]
    (R S : X → Measure Y) [∀ x, IsProbabilityMeasure (R x)]
    [∀ x, IsProbabilityMeasure (S x)] (hR : Measurable R) (hS : Measurable S) :
    (∀ᵐ x ∂ν, R x = S x) ↔ InputTests ν R S := by
  constructor
  · intro h t φ _ _
    calc
      _ = ∫ _ : X, (0 : ℝ) ∂ν := integral_congr_ae (h.mono (fun x hx => by
        simp [discrepancy, hx]))
      _ = 0 := by simp
  · intro h
    have he (t : Y) : ∀ᵐ x ∂ν, discrepancy R S t x = 0 := by
      have hm : Measurable (discrepancy R S t) :=
        ((Measure.measurable_coe (measurableSet_singleton t)).comp hR).ennreal_toReal.sub
          (((Measure.measurable_coe (measurableSet_singleton t)).comp hS).ennreal_toReal)
      have hi : Integrable (discrepancy R S t) ν :=
        (integrable_const (2 : ℝ)).mono' hm.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs, discrepancy]
            exact (abs_sub ((R x).real {t}) ((S x).real {t})).trans (by
              rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
              linarith [measureReal_le_one (μ := R x) (s := {t}),
                measureReal_le_one (μ := S x) (s := {t})])))
      apply hi.ae_eq_zero_of_forall_setIntegral_eq_zero
      intro E hE _
      have hφ : ∃ M : ℝ, ∀ x : X, |E.indicator (fun _ => (1 : ℝ)) x| ≤ M := by
        refine ⟨1, fun x => ?_⟩
        by_cases hx : x ∈ E <;> simp [hx]
      have ht := h t (E.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hE) hφ
      simpa only [← Set.indicator_mul_left, one_mul, integral_indicator hE] using ht
    filter_upwards [ae_all_iff.mpr he] with x hx
    apply Measure.ext_of_measureReal_singleton
    intro t
    exact sub_eq_zero.mp (hx t)

/-- Tests quantify over all bounded Borel functions of the entire input descriptor.
Only the countable complete atom family is synchronized almost everywhere. -/
theorem normalizedB_iff_input_tests (ν : Measure PDescriptor) [IsProbabilityMeasure ν]
    (B : Kernel PDescriptor BDescriptor) [IsMarkovKernel B] :
    (∀ᵐ Q ∂ν, residualB Q = (lawKernel .beta) ∘ₘ B Q) ↔
      InputTests ν residualB (fun Q => (lawKernel .beta) ∘ₘ B Q) := by
  exact probability_input_tests ν residualB (fun Q => (lawKernel .beta) ∘ₘ B Q)
    residualB_measurable (Kernel.comp (lawKernel .beta) B).measurable

theorem normalizedA_iff_input_tests (ν : Measure BDescriptor) [IsProbabilityMeasure ν]
    (A : Kernel BDescriptor PDescriptor) [IsMarkovKernel A] :
    (∀ᵐ W ∂ν, residualA W = (lawKernel .p) ∘ₘ A W) ↔
      InputTests ν residualA (fun W => (lawKernel .p) ∘ₘ A W) := by
  exact probability_input_tests ν residualA (fun W => (lawKernel .p) ∘ₘ A W)
    residualA_measurable (Kernel.comp (lawKernel .p) A).measurable

private theorem coordinate_integrable {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (s : ActivePhase)
    (t : ValidTail s) (R : X → Measure (ValidTail s))
    [∀ x, IsProbabilityMeasure (R x)] (hR : Measurable R) :
    Integrable (fun x => (R x).real {t}) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (((Measure.measurable_coe (measurableSet_singleton t)).comp hR).ennreal_toReal.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖(R x).real {t}‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one)

private theorem barycenter_real {s t : ActivePhase}
    (K : Kernel (RegularDescriptor s) (RegularDescriptor t)) [IsMarkovKernel K]
    (x : RegularDescriptor s) (a : ValidTail t) :
    ((lawKernel t) ∘ₘ K x).real {a} = ∫ y, (law y).real {a} ∂K x := by
  rw [Measure.real, Measure.bind_apply (measurableSet_singleton _) (lawKernel t).aemeasurable]
  exact (integral_toReal ((Measure.measurable_coe (measurableSet_singleton _)).comp
    (measurable_law t)).aemeasurable (Filter.Eventually.of_forall (fun y => by
      exact measure_lt_top (law y) {a}))).symm

/-- Fubini uses one fixed joint realization simultaneously for every bounded input test. -/
theorem input_test_joint_identity {s t : ActivePhase}
    (ν : Measure (RegularDescriptor s)) [IsProbabilityMeasure ν]
    (K : Kernel (RegularDescriptor s) (RegularDescriptor t)) [IsMarkovKernel K]
    (Γ : Measure (RegularDescriptor s × RegularDescriptor t)) (hΓ : Γ = ν ⊗ₘ K)
    (R : RegularDescriptor s → Measure (ValidTail t))
    [∀ x, IsProbabilityMeasure (R x)] (hR : Measurable R)
    (a : ValidTail t) (φ : RegularDescriptor s → ℝ) (hφ : Measurable φ)
    (hbound : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    (∫ x, φ x * discrepancy R (fun x => (lawKernel t) ∘ₘ K x) a x ∂ν) =
      ∫ z, φ z.1 * ((R z.1).real {a} - (law z.2).real {a}) ∂Γ := by
  obtain ⟨M, hM⟩ := hbound
  have hcoord := (Measure.measurable_coe (measurableSet_singleton a)).comp (measurable_law t)
  have hm : Measurable (fun z : RegularDescriptor s × RegularDescriptor t =>
      φ z.1 * ((R z.1).real {a} - (law z.2).real {a})) :=
    (hφ.comp measurable_fst).mul ((((Measure.measurable_coe
      (measurableSet_singleton a)).comp (hR.comp measurable_fst)).ennreal_toReal).sub
        ((hcoord.comp measurable_snd).ennreal_toReal))
  have hi : Integrable (fun z : RegularDescriptor s × RegularDescriptor t =>
      φ z.1 * ((R z.1).real {a} - (law z.2).real {a})) (ν ⊗ₘ K) := by
    apply (integrable_const (M * 2)).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      apply mul_le_mul (hM _) _ (abs_nonneg _) (le_trans (abs_nonneg (φ z.1)) (hM z.1))
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
        linarith [measureReal_le_one (μ := R z.1) (s := {a}),
          measureReal_le_one (μ := law z.2) (s := {a})]))
  rw [hΓ, Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change φ x * discrepancy R (fun x => (lawKernel t) ∘ₘ K x) a x =
      ∫ y, φ x * ((R x).real {a} - (law y).real {a}) ∂K x
    rw [integral_const_mul, integral_sub (integrable_const _)
      (coordinate_integrable (K x) t a law (measurable_law t)), integral_const]
    simp only [probReal_univ, one_smul, discrepancy, barycenter_real])


def JointInputTests {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Γ : Measure (X × Y)) (H : Z → X × Y → ℝ) : Prop :=
  ∀ (a : Z) (φ : X → ℝ), Measurable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
    ∫ z, φ z.1 * H a z ∂Γ = 0

private theorem bounded_mul {X : Type*} (f h : X → ℝ)
    (hf : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hh : ∃ M : ℝ, ∀ x, |h x| ≤ M) :
    ∃ M : ℝ, ∀ x, |f x * h x| ≤ M := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hh
  refine ⟨M * N, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM x) (hN x) (abs_nonneg _) ((abs_nonneg _).trans (hM x))

private theorem joint_scale_iff {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Γ : Measure (X × Y)) (H : Z → X × Y → ℝ) (d : X → ℝ) (hd : Measurable d)
    (hpos : ∀ x, 0 < d x) (hb : ∃ M : ℝ, ∀ x, |d x| ≤ M)
    (hi : ∃ M : ℝ, ∀ x, |(d x)⁻¹| ≤ M) :
    JointInputTests Γ H ↔ JointInputTests Γ (fun a z => d z.1 * H a z) := by
  constructor
  · intro h a φ hφ hbound
    have ht := h a (fun x => φ x * d x) (hφ.mul hd) (bounded_mul φ d hbound hb)
    convert ht using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by ring)
  · intro h a φ hφ hbound
    have ht := h a (fun x => φ x * (d x)⁻¹) (hφ.mul hd.inv)
      (bounded_mul φ (fun x => (d x)⁻¹) hbound hi)
    convert ht using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      field_simp [ne_of_gt (hpos z.1)])

private theorem marginal_joint_iff {s t : ActivePhase}
    (ν : Measure (RegularDescriptor s)) [IsProbabilityMeasure ν]
    (K : Kernel (RegularDescriptor s) (RegularDescriptor t)) [IsMarkovKernel K]
    (Γ : Measure (RegularDescriptor s × RegularDescriptor t)) (hΓ : Γ = ν ⊗ₘ K)
    (R : RegularDescriptor s → Measure (ValidTail t))
    [∀ x, IsProbabilityMeasure (R x)] (hR : Measurable R) :
    InputTests ν R (fun x => (lawKernel t) ∘ₘ K x) ↔
      JointInputTests Γ (fun a z => (R z.1).real {a} - (law z.2).real {a}) := by
  constructor
  · intro h a φ hφ hb
    rw [← input_test_joint_identity ν K Γ hΓ R hR a φ hφ hb]
    exact h a φ hφ hb
  · intro h a φ hφ hb
    rw [input_test_joint_identity ν K Γ hΓ R hR a φ hφ hb]
    exact h a φ hφ hb

private theorem emission_real_bounds (s : ActivePhase) (D : RegularDescriptor s) :
    (1 / 3 : ℝ) ≤ (emission s D.val).toReal ∧ (emission s D.val).toReal ≤ 2 / 5 := by
  have htop : upper ≠ ∞ := by unfold upper; finiteness
  have hfin : emission s D.val ≠ ∞ := ne_top_of_le_ne_top htop D.property.2.1
  have hl := (ENNReal.toReal_le_toReal (by unfold lower; finiteness) hfin).mpr D.property.1
  have hu := (ENNReal.toReal_le_toReal hfin htop).mpr D.property.2.1
  norm_num [lower, upper] at hl hu
  exact ⟨hl, hu⟩

private theorem denominatorB_bounds (Q : PDescriptor) :
    (3 / 5 : ℝ) ≤ (1 - u Q).toReal ∧ (1 - u Q).toReal ≤ 2 / 3 := by
  have hu : u Q ≤ 1 := Q.property.2.1.trans (by
    apply (ENNReal.toReal_le_toReal (by unfold upper; finiteness) (by simp)).mp
    norm_num [upper])
  rw [ENNReal.toReal_sub_of_le hu (by simp)]
  have h := emission_real_bounds .p Q
  change (1 / 3 : ℝ) ≤ (u Q).toReal ∧ (u Q).toReal ≤ 2 / 5 at h
  norm_num only [ENNReal.toReal_one]
  constructor <;> linarith [h.1, h.2]

private theorem reciprocal_bound {X : Type*} (d : X → ℝ)
    (h : ∀ x, (1 / 3 : ℝ) ≤ d x) : ∃ M : ℝ, ∀ x, |(d x)⁻¹| ≤ M := by
  refine ⟨3, fun x => ?_⟩
  have hp : 0 < d x := lt_of_lt_of_le (by norm_num) (h x)
  rw [abs_of_pos (inv_pos.mpr hp)]
  have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 3) (h x)
  norm_num at hi
  exact hi

private theorem residualB_real (Q : PDescriptor) (a : ValidTail .beta) :
    (residualB Q).real {a} = (1 - u Q).toReal⁻¹ * (law Q).real {prependB a} := by
  simp only [Measure.real, residualB, Measure.smul_apply, smul_eq_mul,
    prependB_embedding.comap_apply, Set.image_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

private theorem residualA_real (W : BDescriptor) (a : ValidTail .p) :
    (residualA W).real {a} = (v W).toReal⁻¹ * (law W).real {prependA a} := by
  simp only [Measure.real, residualA, Measure.smul_apply, smul_eq_mul,
    prependA_embedding.comap_apply, Set.image_singleton, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

/-- The original unnormalized signed tests use this one fixed joint law and unweighted margin. -/
theorem normalizedB_iff_full_joint_tests (ν : Measure PDescriptor) [IsProbabilityMeasure ν]
    (B : Kernel PDescriptor BDescriptor) [IsMarkovKernel B]
    (Γ : Measure (PDescriptor × BDescriptor)) (hΓ : Γ = ν ⊗ₘ B) :
    (∀ᵐ Q ∂ν, residualB Q = (lawKernel .beta) ∘ₘ B Q) ↔
      ∀ (a : ValidTail .beta) (φ : RegularDescriptor .p → ℝ),
        @Measurable _ _ (@borel _ (descriptorTVTopology .p)) inferInstance φ →
        (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
        ∫ z, φ z.1 * ((law z.1).real {prependB a} -
        (1 - u z.1).toReal * (law z.2).real {a}) ∂Γ = 0 := by
  have hi : (∀ᵐ Q ∂ν, residualB Q = (lawKernel .beta) ∘ₘ B Q) ↔
      JointInputTests Γ (fun a z => (law z.1).real {prependB a} -
        (1 - u z.1).toReal * (law z.2).real {a}) := by
    rw [normalizedB_iff_input_tests ν B,
      marginal_joint_iff ν B Γ hΓ residualB residualB_measurable]
    have hp (Q : PDescriptor) : 0 < (1 - u Q).toReal :=
      lt_of_lt_of_le (by norm_num) (denominatorB_bounds Q).1
    rw [joint_scale_iff Γ _ (fun Q => (1 - u Q).toReal)
      (measurable_const.sub measurable_u).ennreal_toReal hp
      ⟨1, fun Q => by rw [abs_of_pos (hp Q)]; linarith [(denominatorB_bounds Q).2]⟩
      (reciprocal_bound _ (fun Q => by linarith [(denominatorB_bounds Q).1]))]
    apply Iff.of_eq
    congr 1
    funext a z
    rw [residualB_real]
    field_simp [ne_of_gt (hp z.1)]
    <;> ring
  rw [descriptor_tv_borel_eq .p]
  simpa only [JointInputTests] using hi

/-- The second phase has the same full joint-test equivalence, with its own original denominator. -/
theorem normalizedA_iff_full_joint_tests (ν : Measure BDescriptor) [IsProbabilityMeasure ν]
    (A : Kernel BDescriptor PDescriptor) [IsMarkovKernel A]
    (Γ : Measure (BDescriptor × PDescriptor)) (hΓ : Γ = ν ⊗ₘ A) :
    (∀ᵐ W ∂ν, residualA W = (lawKernel .p) ∘ₘ A W) ↔
      ∀ (a : ValidTail .p) (φ : RegularDescriptor .beta → ℝ),
        @Measurable _ _ (@borel _ (descriptorTVTopology .beta)) inferInstance φ →
        (∃ M : ℝ, ∀ x, |φ x| ≤ M) →
        ∫ z, φ z.1 * ((law z.1).real {prependA a} -
        (v z.1).toReal * (law z.2).real {a}) ∂Γ = 0 := by
  have hi : (∀ᵐ W ∂ν, residualA W = (lawKernel .p) ∘ₘ A W) ↔
      JointInputTests Γ (fun a z => (law z.1).real {prependA a} -
        (v z.1).toReal * (law z.2).real {a}) := by
    rw [normalizedA_iff_input_tests ν A,
      marginal_joint_iff ν A Γ hΓ residualA residualA_measurable]
    have hb (W : BDescriptor) : (1 / 3 : ℝ) ≤ (v W).toReal ∧ (v W).toReal ≤ 2 / 5 :=
      emission_real_bounds .beta W
    have hp (W : BDescriptor) : 0 < (v W).toReal := lt_of_lt_of_le (by norm_num) (hb W).1
    rw [joint_scale_iff Γ _ (fun W => (v W).toReal) measurable_v.ennreal_toReal hp
      ⟨1, fun W => by rw [abs_of_pos (hp W)]; linarith [(hb W).2]⟩
      (reciprocal_bound _ (fun W => (hb W).1))]
    apply Iff.of_eq
    congr 1
    funext a z
    rw [residualA_real]
    field_simp [ne_of_gt (hp z.1)]
    <;> ring
  rw [descriptor_tv_borel_eq .beta]
  simpa only [JointInputTests] using hi

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelInputTests
