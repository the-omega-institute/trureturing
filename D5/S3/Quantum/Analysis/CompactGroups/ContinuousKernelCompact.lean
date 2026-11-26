/- GID: D5/S3/Quantum/Analysis/CompactGroups/ContinuousKernelCompact
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CompactGroups/ContinuousKernelCompact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral operators with a continuous kernel on compact spaces are compact. -/

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Compactness of integral operators with a continuous kernel

Let `X` and `Y` be compact spaces, `μ` a finite measure on `Y` and `K` a continuous kernel on
`X × Y`. For `1 ≤ p`, the formula `(T f) x = ∫ y, K (x, y) * f y ∂μ` defines a continuous linear
map `T : Lᵖ(μ) → C(X)`, and `T` is a compact operator.

Every `f ∈ Lᵖ(μ)` is integrable with `∫ ‖f‖ ≤ C ‖f‖_p` (finite measure), so
`|(T f) x - (T f) x'| ≤ ‖K (x, ·) - K (x', ·)‖_∞ · C ‖f‖_p`. Since `x ↦ K (x, ·)` is continuous
into `C(Y)` with the sup norm, the image of the unit ball is uniformly bounded and equicontinuous,
and the Arzela-Ascoli theorem gives a compact set containing it.
-/

open MeasureTheory Filter Topology Metric
open scoped BoundedContinuousFunction

namespace D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact

section Helpers

variable {Y 𝕜 : Type*} [MeasurableSpace Y] [RCLike 𝕜] {μ : Measure Y} [IsFiniteMeasure μ]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- The `L¹` norm of an `Lᵖ` function is at most `μ(Y) ^ (1 - 1 / p)` times its `Lᵖ` norm. -/
private lemma integral_norm_le (f : Lp 𝕜 p μ) :
    ∫ y, ‖f y‖ ∂μ ≤
      (μ Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal * ‖f‖ := by
  have hexp : 0 ≤ 1 / (1 : ENNReal).toReal - 1 / p.toReal := by
    rcases eq_or_ne p ⊤ with rfl | hp
    · simp
    · have h1 : (1 : ENNReal).toReal ≤ p.toReal := ENNReal.toReal_mono hp Fact.out
      rw [ENNReal.toReal_one] at h1 ⊢
      exact sub_nonneg.2 (one_div_le_one_div_of_le one_pos h1)
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def, mul_comm,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ _)))
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ Fact.out (Lp.aestronglyMeasurable f))

variable [TopologicalSpace Y] [CompactSpace Y]

/-- Pairing an `Lᵖ` function with a continuous function `g` is bounded by `‖g‖_∞ · ∫ ‖f‖`. -/
private lemma norm_integral_mul_le (g : C(Y, 𝕜)) (f : Lp 𝕜 p μ) :
    ‖∫ y, g y * f y ∂μ‖ ≤ ‖g‖ * ∫ y, ‖f y‖ ∂μ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (((Lp.memLp f).integrable Fact.out).norm.const_mul _)
    (ae_of_all _ fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm y) (norm_nonneg _)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Pointwise bound for the integral of a continuous kernel against an `Lᵖ` function. -/
private lemma norm_integral_kernel_le (K : C(X × Y, 𝕜)) (f : Lp 𝕜 p μ) (x : X) :
    ‖∫ y, K (x, y) * f y ∂μ‖ ≤
      ‖K‖ * ((μ Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal * ‖f‖) := by
  have hK : ‖K.curry x‖ ≤ ‖K‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg K)).2 fun y => K.norm_coe_le_norm (x, y)
  exact (norm_integral_mul_le (K.curry x) f).trans (mul_le_mul hK (integral_norm_le f)
    (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg K))

variable [OpensMeasurableSpace Y]

/-- A continuous function on `Y` times an `Lᵖ` function is integrable. -/
private lemma integrable_mul (g : C(Y, 𝕜)) (f : Lp 𝕜 p μ) :
    Integrable (fun y => g y * f y) μ :=
  ((Lp.memLp f).integrable Fact.out).bdd_mul g.continuous.aestronglyMeasurable
    (ae_of_all _ fun y => g.norm_coe_le_norm y)

/-- Pairing with a fixed `Lᵖ` function is Lipschitz in the continuous function, for the sup
norm, with constant `∫ ‖f‖`. -/
private lemma dist_integral_mul_le (g₁ g₂ : C(Y, 𝕜)) (f : Lp 𝕜 p μ) :
    dist (∫ y, g₁ y * f y ∂μ) (∫ y, g₂ y * f y ∂μ) ≤ dist g₁ g₂ * ∫ y, ‖f y‖ ∂μ := by
  rw [dist_eq_norm, ← integral_sub (integrable_mul g₁ f) (integrable_mul g₂ f), dist_eq_norm]
  simpa only [ContinuousMap.sub_apply, sub_mul] using norm_integral_mul_le (g₁ - g₂) f

omit [CompactSpace X] in
/-- The integral of a continuous kernel against an `Lᵖ` function is continuous. -/
private lemma continuous_integral_kernel (K : C(X × Y, 𝕜)) (f : Lp 𝕜 p μ) :
    Continuous fun x => ∫ y, K (x, y) * f y ∂μ :=
  ((LipschitzWith.of_dist_le' fun g₁ g₂ => (dist_integral_mul_le g₁ g₂ f).trans_eq
      (mul_comm _ _)).continuous.comp K.curry.continuous :)

end Helpers

/-- For compact spaces `X` and `Y` and a finite measure on `Y`, the integral operator of a
continuous kernel on `X × Y` is a compact operator from `Lᵖ` (`1 ≤ p`) into the continuous
functions on `X` with the sup norm. -/
theorem exists_isCompactOperator_kernel {X Y 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [RCLike 𝕜]
    (μ : Measure Y) [IsFiniteMeasure μ] {p : ENNReal} [Fact (1 ≤ p)]
    (K : C(X × Y, 𝕜)) :
    ∃ T : Lp 𝕜 p μ →L[𝕜] C(X, 𝕜), IsCompactOperator T ∧
      ∀ (f : Lp 𝕜 p μ) (x : X), T f x = ∫ y, K (x, y) * f y ∂μ := by
  set C : ℝ := (μ Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  let L : Lp 𝕜 p μ →ₗ[𝕜] C(X, 𝕜) :=
    { toFun := fun f => ⟨fun x => ∫ y, K (x, y) * f y ∂μ, continuous_integral_kernel K f⟩
      map_add' := fun f g => by
        ext x
        change ∫ y, K (x, y) * (f + g) y ∂μ =
          ∫ y, K (x, y) * f y ∂μ + ∫ y, K (x, y) * g y ∂μ
        rw [← integral_add (f := fun y => K (x, y) * f y) (integrable_mul (K.curry x) f)
          (g := fun y => K (x, y) * g y) (integrable_mul (K.curry x) g)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        ext x
        change ∫ y, K (x, y) * (c • f) y ∂μ = c * ∫ y, K (x, y) * f y ∂μ
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm] }
  have hbound : ∀ f : Lp 𝕜 p μ, ‖L f‖ ≤ ‖K‖ * C * ‖f‖ := fun f =>
    (ContinuousMap.norm_le _ (by positivity)).2 fun x =>
      (norm_integral_kernel_le K f x).trans_eq (mul_assoc _ _ _).symm
  let T : Lp 𝕜 p μ →L[𝕜] C(X, 𝕜) := L.mkContinuous (‖K‖ * C) hbound
  refine ⟨T, ?_, fun f x => rfl⟩
  let e := ContinuousMap.isometryEquivBoundedOfCompact X 𝕜
  let A : Set (X →ᵇ 𝕜) := e '' (T '' ball 0 1)
  have hA : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : 𝕜) (‖K‖ * C))
      (isCompact_closedBall _ _) A ?_ ?_
    · rintro _ x ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      rw [mem_closedBall_zero_iff]
      refine (norm_integral_kernel_le K f x).trans ?_
      rw [mem_ball_zero_iff] at hf
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hC0 hf.le) (norm_nonneg K)
    · intro x₀
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
      filter_upwards [Metric.tendsto_nhds.1 (K.curry.continuous.tendsto x₀) _ hδ] with x hx
      rintro ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩⟩
      rw [mem_ball_zero_iff] at hf
      change dist (∫ y, K (x₀, y) * f y ∂μ) (∫ y, K (x, y) * f y ∂μ) < ε
      have hN : ∫ y, ‖f y‖ ∂μ ≤ C := (integral_norm_le f).trans (mul_le_of_le_one_right hC0 hf.le)
      calc dist (∫ y, K (x₀, y) * f y ∂μ) (∫ y, K (x, y) * f y ∂μ)
        _ ≤ dist (K.curry x₀) (K.curry x) * ∫ y, ‖f y‖ ∂μ :=
            dist_integral_mul_le (K.curry x₀) (K.curry x) f
        _ ≤ ε / (C + 1) * C := by
          rw [dist_comm] at hx
          exact mul_le_mul hx.le hN (integral_nonneg fun _ => norm_nonneg _) hδ.le
        _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          exact mul_lt_mul_of_pos_left (lt_add_one C) hε
  refine ⟨e.symm '' closure A, hA.image e.symm.continuous,
    mem_of_superset (ball_mem_nhds 0 one_pos) fun f hf =>
      ⟨e (T f), subset_closure ⟨T f, ⟨f, hf, rfl⟩, rfl⟩, e.symm_apply_apply _⟩⟩

end D5.S3.Quantum.Analysis.CompactGroups.ContinuousKernelCompact
