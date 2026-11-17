/- GID: D5/S3/Quantum/Divergence/NormalOverlapCurvatureEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/NormalOverlapCurvatureEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal closed-curvature costs of actual normal posterior overlaps. -/

import D5.S3.Quantum.Divergence.NormalOverlapCompatibility
import Mathlib.MeasureTheory.Measure.Support

/-! The full closed perspective is compared through actual overlap coordinates. -/

noncomputable section
universe u v
open Set MeasureTheory
open scoped ComplexOrder Topology ENNReal
open D5.S3.Quantum.Analysis.NormalMomentFamily
open D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
open D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
open D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
open D5.S3.Quantum.Divergence.NormalOverlapCompatibility
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Analytic.Convexity.PosteriorCurvatureCost

namespace D5.S3.Quantum.Divergence.NormalOverlapCurvatureEquality

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem overlap_mass_integral {ρ σ : StrongDual ℂ A}
    (F : Family ρ σ) (t : ℝ) :
    (overlap F t 1).re = ∫ x : Interval, min x.val (t * (1 - x.val)) ∂scalarMeasure F := by
  have h := integral_complex F (overlapFunction t)
  change overlap F t 1 = ∫ x, ((min x.val (t * (1 - x.val)) : ℝ) : ℂ) ∂scalarMeasure F at h
  rw [integral_complex_ofReal] at h
  exact congrArg Complex.re h

private theorem family_masses {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    (∫ x : Interval, x.val ∂scalarMeasure F) = (ρ 1).re ∧
      (∫ x : Interval, (1 - x.val) ∂scalarMeasure F) = (σ 1).re := by
  have hl := integral_complex F posterior
  rw [posterior_value] at hl
  change ρ 1 = ∫ x, (x.val : ℂ) ∂scalarMeasure F at hl
  rw [integral_complex_ofReal] at hl
  have hr := integral_complex F (1 - posterior)
  rw [map_sub, unit_value, posterior_value] at hr
  have he : (ρ + σ) - ρ = σ := by abel
  rw [he] at hr
  have hg : (fun x : Interval => (1 - posterior) x) =
      (fun x => ((1 - x.val : ℝ) : ℂ)) := by ext x; simp [posterior]
  rw [hg, integral_complex_ofReal] at hr
  exact ⟨(congrArg Complex.re hl).symm, (congrArg Complex.re hr).symm⟩

/-- The two actual posterior hinge integrals are the mass deficits of the
functional overlap. Both endpoints x=0 and x=1 are retained. -/
theorem family_hinge_integrals {ρ σ : StrongDual ℂ A} (F : Family ρ σ) (t : ℝ) :
    (∫⁻ x : Interval, ENNReal.ofReal (t * (1 - x.val) - x.val) ∂scalarMeasure F) =
        ENNReal.ofReal (t * (σ 1).re - (overlap F t 1).re) ∧
    (∫⁻ x : Interval, ENNReal.ofReal (x.val - t * (1 - x.val)) ∂scalarMeasure F) =
        ENNReal.ofReal ((ρ 1).re - (overlap F t 1).re) := by
  have hm := family_masses F
  have hi (g : C(Interval, ℝ)) : Integrable g (scalarMeasure F) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hx : Integrable (fun x : Interval => x.val) (scalarMeasure F) :=
    hi ⟨fun x => x.val, by fun_prop⟩
  have hq : Integrable (fun x : Interval => 1 - x.val) (scalarMeasure F) :=
    hi ⟨fun x => 1 - x.val, by fun_prop⟩
  have hmin : Integrable (fun x : Interval => min x.val (t * (1 - x.val))) (scalarMeasure F) :=
    hi ⟨fun x => min x.val (t * (1 - x.val)), by fun_prop⟩
  have hminus (x : Interval) : t * (1 - x.val) - min x.val (t * (1 - x.val)) =
      max (t * (1 - x.val) - x.val) 0 := by
    rcases le_total x.val (t * (1 - x.val)) with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    · rw [min_eq_right h, sub_self, max_eq_right (sub_nonpos.mpr h)]
  have hplus (x : Interval) : x.val - min x.val (t * (1 - x.val)) =
      max (x.val - t * (1 - x.val)) 0 := by
    rcases le_total x.val (t * (1 - x.val)) with h | h
    · rw [min_eq_left h, sub_self, max_eq_right (sub_nonpos.mpr h)]
    · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  constructor
  · have h := ofReal_integral_eq_lintegral_ofReal ((hq.const_mul t).sub hmin)
      (Filter.Eventually.of_forall (fun x => sub_nonneg.mpr (min_le_right _ _)))
    simp only [Pi.sub_apply] at h
    rw [integral_sub (hq.const_mul t) hmin, integral_const_mul, hm.2, ← overlap_mass_integral] at h
    simpa [hminus] using h.symm
  · have h := ofReal_integral_eq_lintegral_ofReal (hx.sub hmin)
      (Filter.Eventually.of_forall (fun x => sub_nonneg.mpr (min_le_left _ _)))
    simp only [Pi.sub_apply] at h
    rw [integral_sub hx hmin, hm.1, ← overlap_mass_integral] at h
    simpa [hplus] using h.symm

/-- The literal original closed-perspective objective equals its exact overlap
curvature profile. The whole atom at one is in the lower branch. No endpoint
integrability or finite-cost premise is used. -/
theorem familyCost_eq_overlap_curvature {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    familyCost hf F = (affineCost f ρ σ : EReal) +
      (((∫⁻ t in Iic (⟨1, by norm_num⟩ : Positive),
          ENNReal.ofReal ((t : ℝ) * (σ 1).re - (overlap F t 1).re) ∂curvature hf) +
        ∫⁻ t in Ioi (⟨1, by norm_num⟩ : Positive),
          ENNReal.ofReal ((ρ 1).re - (overlap F t 1).re) ∂curvature hf : ℝ≥0∞) : EReal) := by
  rw [familyCost_eq_affine]
  change (affineCost f ρ σ : EReal) +
    ((∫⁻ x : Interval, curvatureRemainder hf x.val (1 - x.val) ∂scalarMeasure F : ℝ≥0∞) : EReal) = _
  rw [integral_curvatureRemainder hf (scalarMeasure F)
    (p := fun x : Interval => x.val) (q := fun x => 1 - x.val)
    measurable_subtype_coe (measurable_const.sub measurable_subtype_coe)]
  congr 3
  · apply lintegral_congr
    intro t
    exact (family_hinge_integrals F t).1
  · apply lintegral_congr
    intro t
    exact (family_hinge_integrals F t).2

section Concrete
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)

/-- The literal original maximal value, over every fixed-universe sigma-finite
source and every algebraic standard-predual preparation on its whole complex L1. -/
def maximalValue {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) : EReal :=
  sInf (standardAttainableCosts.{u} M hf ρ σ)

/-- Curvature integral of the actual optimal normal-overlap mass deficits.
The operational single-hinge identification is a separate proof obligation. -/
def hockeyValue {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) : EReal :=
  (affineCost f ρ σ : EReal) +
    (((∫⁻ t in Iic (⟨1, by norm_num⟩ : Positive),
        ENNReal.ofReal ((t : ℝ) * (σ 1).re - overlapValue M ρ σ t) ∂curvature hf) +
      ∫⁻ t in Ioi (⟨1, by norm_num⟩ : Positive),
        ENNReal.ofReal ((ρ 1).re - overlapValue M ρ σ t) ∂curvature hf : ℝ≥0∞) : EReal)

variable (hρ : Positive ρ) (hσ : Positive σ)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)
include hρ hσ hρs hσs

private theorem overlap_le_value (F : Family ρ σ) (t : Positive) :
    (overlap F t 1).re ≤ overlapValue M ρ σ t := by
  obtain ⟨_, _, hmax⟩ := value_attained M ρ σ hρ hσ hρs hσs t t.property
  obtain ⟨hp, hl, hr⟩ := overlap_feasible F t t.property.le
  exact hmax (overlap F t) hp hl hr

private def deficitKernel (a : Positive → ℝ) (t : Positive) : ℝ≥0∞ :=
  if (t : ℝ) ≤ 1 then ENNReal.ofReal ((t : ℝ) * (σ 1).re - a t)
  else ENNReal.ofReal ((ρ 1).re - a t)

private theorem deficitKernel_integral {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (a : Positive → ℝ) :
    (∫⁻ t, deficitKernel M ρ σ a t ∂curvature hf) =
      (∫⁻ t in Iic (⟨1, by norm_num⟩ : Positive),
        ENNReal.ofReal ((t : ℝ) * (σ 1).re - a t) ∂curvature hf) +
      ∫⁻ t in Ioi (⟨1, by norm_num⟩ : Positive),
        ENNReal.ofReal ((ρ 1).re - a t) ∂curvature hf := by
  have he : deficitKernel M ρ σ a =
      (Iic (⟨1, by norm_num⟩ : Positive)).piecewise
        (fun t => ENNReal.ofReal ((t : ℝ) * (σ 1).re - a t))
        (fun t => ENNReal.ofReal ((ρ 1).re - a t)) := by
    funext t
    rfl
  rw [he, lintegral_piecewise measurableSet_Iic.nullMeasurableSet, compl_Iic]

private theorem continuous_overlap_profile (F : Family ρ σ) :
    Continuous (fun t : Positive => (overlap F t 1).re) := by
  have hc : Continuous (fun t : ℝ =>
      ∫ x : Interval, min x.val (t * (1 - x.val)) ∂scalarMeasure F) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (f := fun t : ℝ => fun x : Interval => min x.val (t * (1 - x.val)))
        (by fun_prop) isCompact_univ (μ := scalarMeasure F))
  simpa only [overlap_mass_integral, Function.comp_def] using
    hc.comp (continuous_subtype_val : Continuous (fun t : Positive => (t : ℝ)))

private theorem value_upper_bounds (t : Positive) :
    overlapValue M ρ σ t ≤ (ρ 1).re ∧
      overlapValue M ρ σ t ≤ (t : ℝ) * (σ 1).re := by
  obtain ⟨F, he, _⟩ := value_attained M ρ σ hρ hσ hρs hσs t t.property
  obtain ⟨_, hl, hr⟩ := overlap_feasible F t t.property.le
  have hreal {z w : ℂ} (h : z ≤ w) : z.re ≤ w.re := by
    have hh := (Complex.nonneg_iff.mp (sub_nonneg.mpr h)).1
    simpa only [Complex.sub_re, sub_nonneg] using hh
  rw [← he]
  exact ⟨hreal (hl 1 zero_le_one), by
    simpa only [smul_apply, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hreal (hr 1 zero_le_one)⟩

private theorem hockey_le_familyCost {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (F : Family ρ σ) : hockeyValue M ρ σ hf ≤ familyCost hf F := by
  rw [familyCost_eq_overlap_curvature, hockeyValue]
  apply add_le_add le_rfl
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  apply add_le_add
  · apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (overlap_le_value M ρ σ hρ hσ hρs hσs F t) _)
  · apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (overlap_le_value M ρ σ hρ hσ hρs hσs F t) _)

private theorem hockey_le_maximal {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    hockeyValue M ρ σ hf ≤ maximalValue.{u} M ρ σ hf := by
  rw [maximalValue, standardAttainableCosts_eq_range M ρ σ hρ hσ hρs hσs hf]
  apply le_sInf
  rintro z ⟨F, rfl⟩
  exact hockey_le_familyCost M ρ σ hρ hσ hρs hσs hf F

/-- The literal maximal infimum being real finite already forces the entire
optimal-overlap curvature value to be real finite, without endpoint assumptions. -/
theorem hockey_real_of_maximal_real {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ hf = (c : EReal)) :
    ∃ h : ℝ, hockeyValue M ρ σ hf = (h : EReal) := by
  obtain ⟨c, hc⟩ := hfinite
  have hu : hockeyValue M ρ σ hf ≤ (c : EReal) :=
    (hockey_le_maximal.{u} M ρ σ hρ hσ hρs hσs hf).trans_eq hc
  have hl : (affineCost f ρ σ : EReal) ≤ hockeyValue M ρ σ hf := by
    unfold hockeyValue
    apply le_add_of_nonneg_right
    positivity
  have ht := ne_top_of_le_ne_top (EReal.coe_ne_top c) hu
  have hb := ne_bot_of_le_ne_bot (EReal.coe_ne_bot (affineCost f ρ σ)) hl
  exact ⟨_, (EReal.coe_toReal ht hb).symm⟩

private theorem support_optimal_cost {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (F : Family ρ σ)
    (hF : ∀ t ∈ (curvature hf).support,
      (overlap F t 1).re = overlapValue M ρ σ t) :
    familyCost hf F = hockeyValue M ρ σ hf := by
  rw [familyCost_eq_overlap_curvature, hockeyValue]
  congr 3
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (curvature hf).support_mem_ae] with t ht
    rw [hF t ht]
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (curvature hf).support_mem_ae] with t ht
    rw [hF t ht]

/-- Finite compatibility on the actual curvature support gives literal
standard-original maximal equality with the optimal-overlap curvature formula,
and a single posterior family attaining that value and every support optimum.
This direction even allows an infinite value. The identification of hockeyValue
with original single-hinge operational infima is not part of this declaration. -/
theorem finite_compatibility_implies_original_equality
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hK : FiniteCompatibility M ρ σ (curvature hf).support) :
    maximalValue.{u} M ρ σ hf = hockeyValue M ρ σ hf ∧
      ∃ F : Family ρ σ,
        familyCost hf F = maximalValue.{u} M ρ σ hf ∧
        ∀ t ∈ (curvature hf).support,
          (overlap F t 1).re = overlapValue M ρ σ t := by
  obtain ⟨F, hF⟩ := (finite_compatibility_iff_simultaneous M ρ σ hρ hσ hρs hσs
    (curvature hf).support).mp hK
  have he := support_optimal_cost M ρ σ hρ hσ hρs hσs hf F hF
  have hmem : familyCost hf F ∈ standardAttainableCosts.{u} M hf ρ σ := by
    rw [standardAttainableCosts_eq_range M ρ σ hρ hσ hρs hσs hf]
    exact Set.mem_range_self F
  have hupper : maximalValue.{u} M ρ σ hf ≤ hockeyValue M ρ σ hf :=
    (sInf_le hmem).trans_eq he
  have hlower := hockey_le_maximal.{u} M ρ σ hρ hσ hρs hσs hf
  have heq := le_antisymm hupper hlower
  exact ⟨heq, F, he.trans heq.symm, hF⟩

set_option maxHeartbeats 800000 in
/-- A real-finite minimizing actual family can have cost equal to the
optimal-overlap curvature formula only when it maximizes EVERY support overlap.
The argument compares it to actual alternative families; it assumes neither
measurability nor continuity of an externally supplied optimal scalar profile. -/
theorem minimizing_equality_implies_support_optimal
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (F : Family ρ σ)
    (hcost : familyCost hf F = hockeyValue M ρ σ hf)
    (hfinite : ∃ c : ℝ, familyCost hf F = (c : EReal)) :
    ∀ t ∈ (curvature hf).support, (overlap F t 1).re = overlapValue M ρ σ t := by
  let k := deficitKernel M ρ σ (fun t => (overlap F t 1).re)
  let v := deficitKernel M ρ σ (fun t => overlapValue M ρ σ t)
  have hFC : familyCost hf F = (affineCost f ρ σ : EReal) +
      ((∫⁻ t, k t ∂curvature hf : ℝ≥0∞) : EReal) := by
    rw [familyCost_eq_overlap_curvature, ← deficitKernel_integral M ρ σ hρ hσ hρs hσs hf]
  have hHC : hockeyValue M ρ σ hf = (affineCost f ρ σ : EReal) +
      ((∫⁻ t, v t ∂curvature hf : ℝ≥0∞) : EReal) := by
    rw [hockeyValue, ← deficitKernel_integral M ρ σ hρ hσ hρs hσs hf]
  have heint : (∫⁻ t, k t ∂curvature hf) = ∫⁻ t, v t ∂curvature hf := by
    have he := congrArg (fun z : EReal => z - (affineCost f ρ σ : ℝ)) hcost
    rw [hFC, hHC, EReal.add_sub_cancel_left, EReal.add_sub_cancel_left] at he
    exact EReal.coe_ennreal_injective he
  have hvfin : (∫⁻ t, v t ∂curvature hf) ≠ ∞ := by
    intro hv
    obtain ⟨c, hc⟩ := hfinite
    have hh : familyCost hf F = ⊤ := by rw [hFC, heint, hv]; simp
    exact EReal.coe_ne_top c (hc.symm.trans hh)
  have hcompare (G : Family ρ σ) :
      ∀ t ∈ (curvature hf).support, (overlap G t 1).re ≤ (overlap F t 1).re := by
    let g : Positive → ℝ≥0∞ := fun t =>
      ENNReal.ofReal (max ((overlap G t 1).re - (overlap F t 1).re) 0)
    have hg : Continuous g := ENNReal.continuous_ofReal.comp
      (((continuous_overlap_profile M ρ σ hρ hσ hρs hσs G).sub
        (continuous_overlap_profile M ρ σ hρ hσ hρs hσs F)).max continuous_const)
    have hpoint (t : Positive) : v t + g t ≤ k t := by
      have hF := overlap_le_value M ρ σ hρ hσ hρs hσs F t
      have hG := overlap_le_value M ρ σ hρ hσ hρs hσs G t
      have hu := value_upper_bounds M ρ σ hρ hσ hρs hσs t
      dsimp only [v, k, deficitKernel, g]
      split_ifs with ht
      · rw [← ENNReal.ofReal_add (sub_nonneg.mpr hu.2) (le_max_right _ _)]
        apply ENNReal.ofReal_le_ofReal
        exact add_le_of_le_sub_left (by
          apply max_le <;> linarith)
      · rw [← ENNReal.ofReal_add (sub_nonneg.mpr hu.1) (le_max_right _ _)]
        apply ENNReal.ofReal_le_ofReal
        exact add_le_of_le_sub_left (by
          apply max_le <;> linarith)
    have hzero : ∫⁻ t, g t ∂curvature hf = 0 := by
      have hle := lintegral_mono (μ := curvature hf) hpoint
      rw [lintegral_add_right _ hg.measurable, heint] at hle
      exact (ENNReal.cancel_of_ne hvfin).add_le_iff_nonpos_right.mp hle |>.antisymm bot_le
    have hae : ∀ᵐ t ∂curvature hf, g t = 0 := (lintegral_eq_zero_iff hg.measurable).mp hzero
    intro t ht
    by_contra hbad
    have hgt : 0 < g t := by
      dsimp only [g]
      exact ENNReal.ofReal_pos.mpr (lt_max_of_lt_left (sub_pos.mpr (lt_of_not_ge hbad)))
    let U : Set Positive := {x | 0 < g x}
    have hU : IsOpen U := isOpen_lt continuous_const hg
    have hpos : 0 < (curvature hf) U :=
      ((curvature hf).mem_support_iff_forall t).mp ht U (hU.mem_nhds hgt)
    have hnull : (curvature hf) U = 0 := by
      apply measure_mono_null (show U ⊆ {x | g x ≠ 0} from fun x hx => ne_of_gt hx)
      simpa only [ae_iff] using hae
    exact (ne_of_gt hpos) hnull
  intro t ht
  obtain ⟨G, hG, _⟩ := value_attained M ρ σ hρ hσ hρs hσs t t.property
  exact le_antisymm (overlap_le_value M ρ σ hρ hσ hρs hσs F t)
    (hG ▸ hcompare G t ht)

/-- The arbitrary-support classification against the exact optimal-overlap
curvature formula, for the literal real-finite standard-original maximal value.
The remaining operational single-hinge identification is deliberately separate. -/
theorem original_equality_iff_finite_compatibility
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hfinite : ∃ c : ℝ, maximalValue.{u} M ρ σ hf = (c : EReal)) :
    maximalValue.{u} M ρ σ hf = hockeyValue M ρ σ hf ↔
      FiniteCompatibility M ρ σ (curvature hf).support := by
  constructor
  · intro heq
    obtain ⟨F, hF, _⟩ := standard_original_reverse_test_extended_attainment.{u}
      M ρ σ hρ hσ hρs hσs hf
    apply (finite_compatibility_iff_simultaneous M ρ σ hρ hσ hρs hσs (curvature hf).support).mpr
    refine ⟨F, minimizing_equality_implies_support_optimal M ρ σ hρ hσ hρs hσs hf F
      (hF.trans heq) ?_⟩
    obtain ⟨c, hc⟩ := hfinite
    exact ⟨c, hF.trans hc⟩
  · intro hK
    exact (finite_compatibility_implies_original_equality.{u} M ρ σ hρ hσ hρs hσs hf hK).1

end Concrete

#print axioms family_hinge_integrals
#print axioms familyCost_eq_overlap_curvature
#print axioms finite_compatibility_implies_original_equality
#print axioms minimizing_equality_implies_support_optimal
#print axioms original_equality_iff_finite_compatibility

end D5.S3.Quantum.Divergence.NormalOverlapCurvatureEquality
