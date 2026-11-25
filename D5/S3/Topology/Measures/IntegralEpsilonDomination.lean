/- GID: D5/S3/Topology/Measures/IntegralEpsilonDomination
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/IntegralEpsilonDomination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Epsilon-dependent integrable controls give full integral convergence. -/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-! # Integral convergence under epsilon-dependent domination

Nonnegative functions converging almost everywhere to zero have vanishing
integrals when, for every positive epsilon, they are bounded by epsilon times
a uniformly integral-bounded family plus a fixed integrable function. Both
controlling families may depend on epsilon, on an arbitrary measure space.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Topology

namespace D5.S3.Topology.Measures.IntegralEpsilonDomination

universe u

/-- Integral convergence with controls that may vary with epsilon. -/
theorem tendsto_integral_of_epsilon_domination {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (M : ℝ)
    (hf : ∀ n, Integrable (f n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0))
    (hf_nonneg : ∀ n x, 0 ≤ f n x)
    (hcontrol : ∀ ε : ℝ, 0 < ε → ∃ (a : ℕ → Ω → ℝ) (b : Ω → ℝ),
      (∀ n, Integrable (a n) μ) ∧ Integrable b μ ∧
      (∀ n x, 0 ≤ a n x) ∧ (∀ x, 0 ≤ b x) ∧
      (∀ n, ∫ x, a n x ∂μ ≤ M) ∧
      (∀ n x, f n x ≤ ε * a n x + b x)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0) := by
  have hM : 0 ≤ M := by
    obtain ⟨a, _, _, _, ha_nonneg, _, henergy, _⟩ := hcontrol 1 zero_lt_one
    exact (integral_nonneg (ha_nonneg 0)).trans (henergy 0)
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall fun n => hc.trans_le (integral_nonneg (hf_nonneg n))
  · intro η hη
    let ε : ℝ := η / (2 * (M + 1))
    have hε : 0 < ε := div_pos hη (by linarith)
    obtain ⟨a, b, ha, hb, ha_nonneg, hb_nonneg, henergy, hbound⟩ := hcontrol ε hε
    let F : ℕ → Ω → ℝ := fun n x => max (f n x - ε * a n x) 0
    have hF_nonneg : ∀ n x, 0 ≤ F n x := fun _ _ => le_max_right _ _
    have hFbound : ∀ n x, F n x ≤ b x := by
      intro n x
      apply max_le
      · linarith [hbound n x]
      · exact hb_nonneg x
    have hF_le : ∀ n x, F n x ≤ f n x := by
      intro n x
      apply max_le
      · linarith [mul_nonneg hε.le (ha_nonneg n x)]
      · exact hf_nonneg n x
    have hFi : ∀ n, Integrable (F n) μ := by
      intro n
      apply hb.mono'
      · have hmeas := ((hf n).sub ((ha n).const_mul ε)).aestronglyMeasurable
        simpa only [F, Pi.sub_apply, id_eq] using
          (continuous_id.max continuous_const).comp_aestronglyMeasurable hmeas
      · exact ae_of_all μ (fun x => by
          rw [Real.norm_of_nonneg (hF_nonneg n x)]
          exact hFbound n x)
    have hFlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0) := by
      filter_upwards [hlim] with x hx
      exact squeeze_zero (fun n => hF_nonneg n x) (fun n => hF_le n x) hx
    have hFint : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 0) := by
      have ht := tendsto_setToFun_of_dominated_convergence
        (dominatedFinMeasAdditive_weightedSMul μ) b
        (fun n => (hFi n).aestronglyMeasurable) hb
        (fun n => ae_of_all μ (fun x => by
          rw [Real.norm_of_nonneg (hF_nonneg n x)]
          exact hFbound n x)) hFlim
      simpa only [← integral_eq_setToFun, integral_zero] using ht
    have hεM : ε * M < η / 2 := by
      dsimp [ε]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < 2 * (M + 1))]
      nlinarith
    filter_upwards [(tendsto_order.1 hFint).2 (η / 2) (by linarith)] with n hn
    have hle : ∫ x, f n x ∂μ ≤ ε * M + ∫ x, F n x ∂μ := by
      calc
        _ ≤ ∫ x, ε * a n x + F n x ∂μ := by
          apply integral_mono (hf n) (((ha n).const_mul ε).add (hFi n))
          intro x
          have hm := le_max_left (f n x - ε * a n x) 0
          dsimp [F]
          linarith
        _ = ε * (∫ x, a n x ∂μ) + ∫ x, F n x ∂μ := by
          rw [integral_add ((ha n).const_mul ε) (hFi n), integral_const_mul]
        _ ≤ ε * M + ∫ x, F n x ∂μ := by
          linarith [mul_le_mul_of_nonneg_left (henergy n) hε.le]
    linarith

#print axioms tendsto_integral_of_epsilon_domination

end D5.S3.Topology.Measures.IntegralEpsilonDomination
