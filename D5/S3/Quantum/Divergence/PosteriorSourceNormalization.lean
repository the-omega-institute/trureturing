/- GID: D5/S3/Quantum/Divergence/PosteriorSourceNormalization
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/PosteriorSourceNormalization
   mirror-E: none(waiver:source-normalization-supplier)
   anchors: []
   utility: none
   digest: Weighted posterior sources preserving original complex L1 inputs and extended cost. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickL1Preparation
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Regular

/-! Weighted posterior normalization on the fixed compact interval preserves the
original complex L1 inputs and the closed-perspective integral, including infinite
endpoint costs. This is a source supplier, not an attainment theorem. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexOrder ENNReal NNReal
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickL1Preparation

namespace D5.S3.Quantum.Divergence.PosteriorSourceNormalization

set_option backward.isDefEq.respectTransparency false

abbrev K := Set.Icc (0 : ℝ) 1

variable {X : Type*} [MeasurableSpace X]

/-- Everywhere nonnegative representatives are used before taking the posterior. -/
def mass (p q : X → ℝ) (x : X) : ℝ≥0 := (p x).toNNReal + (q x).toNNReal

/-- The zero fiber is sent to zero; it has zero weighted measure. -/
def theta (p q : X → ℝ) (x : X) : K :=
  ⟨((p x).toNNReal : ℝ) / (mass p q x : ℝ), by
    have hP := (p x).toNNReal.coe_nonneg
    have hQ := (q x).toNNReal.coe_nonneg
    have hr : (mass p q x : ℝ) = ((p x).toNNReal : ℝ) + (q x).toNNReal := rfl
    refine ⟨div_nonneg hP (mass p q x).coe_nonneg, ?_⟩
    by_cases h : (mass p q x : ℝ) = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne (mass p q x).coe_nonneg (Ne.symm h))).mpr
        (by linarith)⟩

private theorem measurable_mass {p q : X → ℝ} (hpm : Measurable p) (hqm : Measurable q) :
    Measurable (mass p q) := hpm.real_toNNReal.add hqm.real_toNNReal

theorem measurable_theta {p q : X → ℝ} (hpm : Measurable p) (hqm : Measurable q) :
    Measurable (theta p q) :=
  (hpm.real_toNNReal.coe_nnreal_real.div (measurable_mass hpm hqm).coe_nnreal_real).subtype_mk

omit [MeasurableSpace X] in
private theorem weighted_representatives (p q : X → ℝ) (x : X) :
    (mass p q x : ℝ) * (theta p q x : ℝ) = ((p x).toNNReal : ℝ) ∧
    (mass p q x : ℝ) * (1 - (theta p q x : ℝ)) = ((q x).toNNReal : ℝ) := by
  have hr : (mass p q x : ℝ) = ((p x).toNNReal : ℝ) + (q x).toNNReal := rfl
  have hP := (p x).toNNReal.coe_nonneg
  have hQ := (q x).toNNReal.coe_nonneg
  by_cases h : (mass p q x : ℝ) = 0
  · have hp : ((p x).toNNReal : ℝ) = 0 := by linarith
    have hq : ((q x).toNNReal : ℝ) = 0 := by linarith
    simp [h, hp, hq]
  · have ht : (mass p q x : ℝ) * (theta p q x : ℝ) = ((p x).toNNReal : ℝ) :=
      mul_div_cancel₀ _ h
    exact ⟨ht, by nlinarith⟩

private theorem weighted_inputs_ae {μ : Measure X} {p q : X → ℝ}
    (hpn : ∀ᵐ x ∂μ, 0 ≤ p x) (hqn : ∀ᵐ x ∂μ, 0 ≤ q x) :
    ∀ᵐ x ∂μ, (mass p q x : ℝ) * (theta p q x : ℝ) = p x ∧
      (mass p q x : ℝ) * (1 - (theta p q x : ℝ)) = q x := by
  filter_upwards [hpn, hqn] with x hp hq
  simpa [Real.toNNReal_of_nonneg hp, Real.toNNReal_of_nonneg hq] using
    weighted_representatives p q x

def weightedMeasure (μ : Measure X) (p q : X → ℝ) : Measure X :=
  μ.withDensity (fun x => (mass p q x : ℝ≥0∞))

/-- The actual pushforward, with no normalization by the total mass. -/
def posteriorMeasure (μ : Measure X) (p q : X → ℝ) : Measure K :=
  (weightedMeasure μ p q).map (theta p q)

private theorem weightedMeasure_eq_original {μ : Measure X} {p q : X → ℝ}
    (hpn : ∀ᵐ x ∂μ, 0 ≤ p x) (hqn : ∀ᵐ x ∂μ, 0 ≤ q x) :
    weightedMeasure μ p q = μ.withDensity (fun x => ENNReal.ofReal (p x + q x)) := by
  apply withDensity_congr_ae
  filter_upwards [hpn, hqn] with x hp hq
  have he : (mass p q x : ℝ) = p x + q x := by
    simp [mass, Real.toNNReal_of_nonneg hp, Real.toNNReal_of_nonneg hq]
  rw [← he, ENNReal.ofReal_coe_nnreal]

/-- The null-set repair does not change the original weighted source. -/
theorem posteriorMeasure_eq_original {μ : Measure X} {p q : X → ℝ}
    (hpn : ∀ᵐ x ∂μ, 0 ≤ p x) (hqn : ∀ᵐ x ∂μ, 0 ≤ q x) :
    posteriorMeasure μ p q =
      (μ.withDensity (fun x => ENNReal.ofReal (p x + q x))).map (theta p q) := by
  rw [posteriorMeasure, weightedMeasure_eq_original hpn hqn]

private theorem weightedMeasure_finite {μ : Measure X} {p q : X → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ) : IsFiniteMeasure (weightedMeasure μ p q) := by
  have hi : Integrable (fun x => (mass p q x : ℝ)) μ :=
    hp.real_toNNReal.add hq.real_toNNReal
  apply isFiniteMeasure_withDensity
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => (mass p q x).coe_nonneg)
  simp only [ENNReal.ofReal_coe_nnreal] at he
  rw [← he]
  exact ENNReal.ofReal_ne_top

theorem posteriorMeasure_finite_regular {μ : Measure X} {p q : X → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ) :
    IsFiniteMeasure (posteriorMeasure μ p q) ∧ (posteriorMeasure μ p q).Regular := by
  have := weightedMeasure_finite hp hq
  have : IsFiniteMeasure (posteriorMeasure μ p q) := inferInstanceAs
    (IsFiniteMeasure ((weightedMeasure μ p q).map (theta p q)))
  exact ⟨inferInstance, inferInstance⟩

private theorem theta_preserving {μ : Measure X} {p q : X → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) :
    MeasurePreserving (theta p q) (weightedMeasure μ p q) (posteriorMeasure μ p q) :=
  ⟨measurable_theta hpm hqm, rfl⟩

/-- A bounded complex-linear map into the original entire complex L1 space.
It reuses the existing density-change map and the standard L1 pullback. -/
def pullContinuous {μ : Measure X} {p q : X → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hp : Integrable p μ) (hq : Integrable q μ) :
    C(K, ℂ) →L[ℂ] (X →₁[μ] ℂ) := by
  letI := (posteriorMeasure_finite_regular hp hq).1
  exact (PositiveTracePreservingL1Map.weightMap (measurable_mass hpm hqm)).comp
    ((Lp.compMeasurePreservingₗᵢ ℂ (theta p q)
      (theta_preserving hpm hqm)).toContinuousLinearMap.comp
      (ContinuousMap.toLp 1 (posteriorMeasure μ p q) ℂ))

theorem pullContinuous_coe {μ : Measure X} {p q : X → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hp : Integrable p μ) (hq : Integrable q μ)
    (g : C(K, ℂ)) :
    pullContinuous hpm hqm hp hq g =ᵐ[μ]
      (fun x => (mass p q x : ℝ) • g (theta p q x)) := by
  have := (posteriorMeasure_finite_regular hp hq).1
  let G := ContinuousMap.toLp 1 (posteriorMeasure μ p q) ℂ g
  let H := Lp.compMeasurePreserving (theta p q) (theta_preserving hpm hqm) G
  have hG : ∀ᵐ x ∂weightedMeasure μ p q, G (theta p q x) = g (theta p q x) :=
    ae_of_ae_map (measurable_theta hpm hqm).aemeasurable
      (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (posteriorMeasure μ p q) g)
  have hH : H =ᵐ[weightedMeasure μ p q] (fun x => g (theta p q x)) :=
    (Lp.coeFn_compMeasurePreserving G (theta_preserving hpm hqm)).trans hG
  have hH' := (ae_withDensity_iff (measurable_mass hpm hqm).coe_nnreal_ennreal).mp hH
  have hJ := PositiveTracePreservingL1Map.weightMap_coe (measurable_mass hpm hqm) H
  change (PositiveTracePreservingL1Map.weightMap (measurable_mass hpm hqm) H) =ᵐ[μ] _
  filter_upwards [hJ, hH'] with x hx hy
  rw [hx]
  by_cases h : mass p q x = 0
  · simp [h]
  · rw [hy (by simpa using h)]
    rfl

theorem pullContinuous_positive {μ : Measure X} {p q : X → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hp : Integrable p μ) (hq : Integrable q μ)
    (g : C(K, ℂ)) (hg : ∀ t, 0 ≤ g t) :
    ∀ᵐ x ∂μ, 0 ≤ pullContinuous hpm hqm hp hq g x := by
  filter_upwards [pullContinuous_coe hpm hqm hp hq g] with x hx
  rw [hx]
  exact smul_nonneg (mass p q x).coe_nonneg (hg _)

theorem integral_pullContinuous {μ : Measure X} {p q : X → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hp : Integrable p μ) (hq : Integrable q μ)
    (g : C(K, ℂ)) :
    (∫ t, g t ∂posteriorMeasure μ p q) = ∫ x, pullContinuous hpm hqm hp hq g x ∂μ := by
  rw [integral_congr_ae (pullContinuous_coe hpm hqm hp hq g)]
  rw [show posteriorMeasure μ p q = (weightedMeasure μ p q).map (theta p q) from rfl,
    integral_map (measurable_theta hpm hqm).aemeasurable g.continuous.aestronglyMeasurable]
  exact integral_withDensity_eq_integral_smul (measurable_mass hpm hqm) _

/-- The fixed interval's complex coordinate. -/
def coordinate : C(K, ℂ) :=
  ⟨fun t => (t.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

/-- These are equalities in the original complex L1 space, before applying any
preparation. In particular an algebraic preparation needs no continuity premise. -/
theorem pullContinuous_moments {μ : Measure X} {p q : X → ℝ}
    (hpm : Measurable p) (hqm : Measurable q) (hp : Integrable p μ) (hq : Integrable q μ)
    (hpn : ∀ᵐ x ∂μ, 0 ≤ p x) (hqn : ∀ᵐ x ∂μ, 0 ≤ q x) :
    pullContinuous hpm hqm hp hq 1 =
        (hp.add hq).ofReal.toL1 (fun x => ((p x + q x : ℝ) : ℂ)) ∧
    pullContinuous hpm hqm hp hq coordinate =
        hp.ofReal.toL1 (fun x => (p x : ℂ)) ∧
    pullContinuous hpm hqm hp hq (1 - coordinate) =
        hq.ofReal.toL1 (fun x => (q x : ℂ)) := by
  have hpC : Integrable (fun x => (p x : ℂ)) μ := hp.ofReal
  have hqC : Integrable (fun x => (q x : ℂ)) μ := hq.ofReal
  have hrC : Integrable (fun x => ((p x + q x : ℝ) : ℂ)) μ := (hp.add hq).ofReal
  have h := weighted_inputs_ae hpn hqn
  refine ⟨?_, ?_, ?_⟩
  · apply Lp.ext
    filter_upwards [pullContinuous_coe hpm hqm hp hq 1,
      hrC.coeFn_toL1, hpn, hqn] with x hx hy hpx hqx
    rw [hx, hy]
    simp [mass, Real.toNNReal_of_nonneg hpx, Real.toNNReal_of_nonneg hqx,
      RCLike.real_smul_eq_coe_mul]
  · apply Lp.ext
    filter_upwards [pullContinuous_coe hpm hqm hp hq coordinate,
      hpC.coeFn_toL1, h] with x hx hy hz
    rw [hx, hy]
    change ((mass p q x : ℝ) : ℂ) * ((theta p q x : ℝ) : ℂ) = (p x : ℂ)
    exact_mod_cast hz.1
  · apply Lp.ext
    filter_upwards [pullContinuous_coe hpm hqm hp hq (1 - coordinate),
      hqC.coeFn_toL1, h] with x hx hy hz
    rw [hx, hy]
    change ((mass p q x : ℝ) : ℂ) * (1 - ((theta p q x : ℝ) : ℂ)) = (q x : ℂ)
    exact_mod_cast hz.2

/-- Exact preservation of the existing closed-perspective cost. The nonnegative
curvature integral may be infinite, including at either endpoint. -/
theorem closedPerspectiveCost_posterior {μ : Measure X} {p q : X → ℝ}
    (hpm : Measurable p) (hqm : Measurable q)
    (hpn : ∀ᵐ x ∂μ, 0 ≤ p x) (hqn : ∀ᵐ x ∂μ, 0 ≤ q x)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    closedPerspectiveCost hf μ p q =
      closedPerspectiveCost hf (posteriorMeasure μ p q)
        (fun t => t.val) (fun t => 1 - t.val) := by
  have hweighted : closedPerspectiveCost hf (weightedMeasure μ p q)
      (fun x => (theta p q x : ℝ)) (fun x => 1 - (theta p q x : ℝ)) =
      closedPerspectiveCost hf μ p q := by
    rw [weightedMeasure, closedPerspectiveCost_withDensity hf (measurable_mass hpm hqm)]
    unfold closedPerspectiveCost
    congr 1
    · congr 1
      apply integral_congr_ae
      filter_upwards [weighted_inputs_ae hpn hqn] with x hx
      rw [hx.1, hx.2]
    · congr 1
      apply lintegral_congr_ae
      filter_upwards [weighted_inputs_ae hpn hqn] with x hx
      rw [hx.1, hx.2]
  have hR : Measurable (fun t : K => curvatureRemainder hf t.val (1 - t.val)) := by
    have hn : Measurable (fun z : K × Positive =>
        ENNReal.ofReal ((z.2 : ℝ) * (1 - z.1.val) - z.1.val)) :=
      (((measurable_subtype_coe.comp measurable_snd).mul
        (measurable_const.sub (measurable_subtype_coe.comp measurable_fst))).sub
          (measurable_subtype_coe.comp measurable_fst)).ennreal_ofReal
    have hp : Measurable (fun z : K × Positive =>
        ENNReal.ofReal (z.1.val - (z.2 : ℝ) * (1 - z.1.val))) :=
      ((measurable_subtype_coe.comp measurable_fst).sub
        ((measurable_subtype_coe.comp measurable_snd).mul
          (measurable_const.sub (measurable_subtype_coe.comp measurable_fst)))).ennreal_ofReal
    exact hn.lintegral_prod_right'.add hp.lintegral_prod_right'
  have ha : Continuous (fun t : K =>
      f 1 * (1 - t.val) + rightDeriv f 1 * (t.val - (1 - t.val))) := by fun_prop
  rw [weightedMeasure_eq_original hpn hqn] at hweighted
  rw [← hweighted, posteriorMeasure_eq_original hpn hqn]
  symm
  unfold closedPerspectiveCost
  rw [integral_map (measurable_theta hpm hqm).aemeasurable ha.aestronglyMeasurable,
    lintegral_map hR (measurable_theta hpm hqm)]

#print axioms pullContinuous_coe
#print axioms pullContinuous_moments
#print axioms integral_pullContinuous
#print axioms closedPerspectiveCost_posterior

end D5.S3.Quantum.Divergence.PosteriorSourceNormalization
