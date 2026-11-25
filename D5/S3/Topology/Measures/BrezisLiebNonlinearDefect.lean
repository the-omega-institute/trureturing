/- GID: D5/S3/Topology/Measures/BrezisLiebNonlinearDefect
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/BrezisLiebNonlinearDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonlinear Brézis–Lieb cancellation without separate integrability. -/

module

public import D5.S3.Topology.Measures.IntegralEpsilonDomination
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith

/-! # Nonlinear Brézis–Lieb cancellation

Continuous complex nonlinearities with epsilon increment bounds admit strong
L1 cancellation on arbitrary measure spaces. The two nonlinear terms need not
be individually integrable; their difference and its defect are integrable.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace D5.S3.Topology.Measures.BrezisLiebNonlinearDefect

universe u

/-- Full nonlinear cancellation, allowing individually nonintegrable terms. -/
theorem brezis_lieb_nonlinear_defect {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (j : ℂ → ℂ) (hj : Continuous j) (hj0 : j 0 = 0)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (φ ψ : ℝ → ℂ → ℝ)
    (hφ : ∀ ε, 0 < ε → ε < ε₀ → Continuous (φ ε) ∧ ∀ z, 0 ≤ φ ε z)
    (hψ : ∀ ε, 0 < ε → ε < ε₀ → ∀ z, 0 ≤ ψ ε z)
    (hincrement : ∀ ε, 0 < ε → ε < ε₀ → ∀ a b : ℂ,
      ‖j (a + b) - j a‖ ≤ ε * φ ε a + ψ ε b)
    (M : ℝ≥0) (g : Ω → ℂ) (v : ℕ → Ω → ℂ)
    (hg : AEStronglyMeasurable g μ) (hv : ∀ n, AEStronglyMeasurable (v n) μ)
    (hv0 : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 0))
    (hjg : Integrable (fun x => j (g x)) μ)
    (hψg : ∀ ε, 0 < ε → ε < ε₀ → Integrable (fun x => ψ ε (g x)) μ)
    (hmass : ∀ ε, 0 < ε → ε < ε₀ → ∀ n,
      ∫⁻ x, ENNReal.ofReal (φ ε (v n x)) ∂μ ≤ (M : ℝ≥0∞)) :
    (∀ n, Integrable (fun x => j (g x + v n x) - j (v n x)) μ ∧
      Integrable (fun x => j (g x + v n x) - j (v n x) - j (g x)) μ) ∧
    Tendsto (fun n => ∫ x, ‖j (g x + v n x) - j (v n x) - j (g x)‖ ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, j (g x + v n x) - j (v n x) ∂μ)
      atTop (𝓝 (∫ x, j (g x) ∂μ)) := by
  have hφi (ε : ℝ) (hε : 0 < ε) (hεlt : ε < ε₀) (n : ℕ) :
      Integrable (fun x => φ ε (v n x)) μ := by
    refine ⟨(hφ ε hε hεlt).1.comp_aestronglyMeasurable (hv n), ?_⟩
    apply (hasFiniteIntegral_iff_ofReal
      (ae_of_all μ (fun x => (hφ ε hε hεlt).2 (v n x)))).2
    exact (hmass ε hε hεlt n).trans_lt ENNReal.coe_lt_top
  have henergy (ε : ℝ) (hε : 0 < ε) (hεlt : ε < ε₀) (n : ℕ) :
      ∫ x, φ ε (v n x) ∂μ ≤ (M : ℝ) := by
    have heq := ofReal_integral_eq_lintegral_ofReal (hφi ε hε hεlt n)
      (ae_of_all μ (fun x => (hφ ε hε hεlt).2 (v n x)))
    have hb := hmass ε hε hεlt n
    rw [← heq, ← ENNReal.ofReal_coe_nnreal] at hb
    exact (ENNReal.ofReal_le_ofReal_iff M.coe_nonneg).1 hb
  let A : ℕ → Ω → ℂ := fun n x => j (g x + v n x) - j (v n x)
  let D : ℕ → Ω → ℂ := fun n x => A n x - j (g x)
  have hAm (n : ℕ) : AEStronglyMeasurable (A n) μ :=
    (hj.comp_aestronglyMeasurable (hg.add (hv n))).sub
      (hj.comp_aestronglyMeasurable (hv n))
  have hAbound (ε : ℝ) (hε : 0 < ε) (hεlt : ε < ε₀) (n : ℕ) (x : Ω) :
      ‖A n x‖ ≤ ε * φ ε (v n x) + ψ ε (g x) := by
    simpa only [A, add_comm (v n x) (g x)] using
      hincrement ε hε hεlt (v n x) (g x)
  have hhalf : 0 < ε₀ / 2 := half_pos hε₀
  have hhalflt : ε₀ / 2 < ε₀ := half_lt_self hε₀
  have hAi (n : ℕ) : Integrable (A n) μ := by
    apply (((hφi (ε₀ / 2) hhalf hhalflt n).const_mul (ε₀ / 2)).add
      (hψg (ε₀ / 2) hhalf hhalflt)).mono' (hAm n)
    exact ae_of_all μ (fun x => hAbound (ε₀ / 2) hhalf hhalflt n x)
  have hDi (n : ℕ) : Integrable (D n) μ := (hAi n).sub hjg
  have hDlim : ∀ᵐ x ∂μ, Tendsto (fun n => D n x) atTop (𝓝 0) := by
    filter_upwards [hv0] with x hx
    have hsum : Tendsto (fun n => g x + v n x) atTop (𝓝 (g x)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := g x)).add hx
    have h₁ := (hj.tendsto (g x)).comp hsum
    have h₂ := (hj.tendsto 0).comp hx
    simpa only [D, A, Function.comp_apply, hj0, sub_zero, sub_self] using
      (h₁.sub h₂).sub_const (j (g x))
  have hnormlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖D n x‖) atTop (𝓝 0) := by
    filter_upwards [hDlim] with x hx
    simpa only [norm_zero] using hx.norm
  have hL1 : Tendsto (fun n => ∫ x, ‖D n x‖ ∂μ) atTop (𝓝 0) := by
    refine IntegralEpsilonDomination.tendsto_integral_of_epsilon_domination μ
      (fun n x => ‖D n x‖) (M : ℝ) (fun n => (hDi n).norm) hnormlim
      (fun n x => norm_nonneg _) ?_
    intro ε hε
    let δ : ℝ := min ε (ε₀ / 2)
    have hδ : 0 < δ := lt_min hε hhalf
    have hδlt : δ < ε₀ := (min_le_right _ _).trans_lt hhalflt
    have hδε : δ ≤ ε := min_le_left _ _
    refine ⟨(fun n x => φ δ (v n x)), (fun x => ψ δ (g x) + ‖j (g x)‖),
      (fun n => hφi δ hδ hδlt n), (hψg δ hδ hδlt).add hjg.norm,
      (fun n x => (hφ δ hδ hδlt).2 (v n x)),
      (fun x => add_nonneg (hψ δ hδ hδlt (g x)) (norm_nonneg _)),
      (fun n => henergy δ hδ hδlt n), ?_⟩
    intro n x
    change ‖A n x - j (g x)‖ ≤ ε * φ δ (v n x) + (ψ δ (g x) + ‖j (g x)‖)
    have hb := hAbound δ hδ hδlt n x
    have he := mul_le_mul_of_nonneg_right hδε ((hφ δ hδ hδlt).2 (v n x))
    have ht := norm_sub_le (A n x) (j (g x))
    linarith
  have hDint : Tendsto (fun n => ∫ x, D n x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => norm_integral_le_integral_norm (D n)) hL1
  have hsplit (n : ℕ) : (∫ x, D n x ∂μ) =
      (∫ x, A n x ∂μ) - (∫ x, j (g x) ∂μ) := by
    simpa only [D] using integral_sub (hAi n) hjg
  have hAint : Tendsto (fun n => ∫ x, A n x ∂μ) atTop (𝓝 (∫ x, j (g x) ∂μ)) := by
    simpa only [hsplit, sub_add_cancel, zero_add] using
      hDint.add_const (∫ x, j (g x) ∂μ)
  exact ⟨fun n => ⟨hAi n, hDi n⟩, hL1, hAint⟩

#print axioms brezis_lieb_nonlinear_defect

end D5.S3.Topology.Measures.BrezisLiebNonlinearDefect
