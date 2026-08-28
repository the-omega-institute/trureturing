/- GID: D5/S3/Constants/Limits/EulerCountertermUniqueness
   generality: G
   mirror-B: D5/B/S3/Constants/Limits/EulerCountertermUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Gamma is the unique harmonic-log counterterm; pi cancels the Gaussian duality defect. -/

-- Library-search audit trail (2026-08-28):
-- * D5's `GaussianSelfDualPi.gaussian_self_dual_iff` exactly characterizes strict Fourier
--   self-duality at scale pi; it is reused for the source's pi contrast.
-- * Pinned Mathlib's `Real.tendsto_harmonic_sub_log` gives the canonical Euler-Mascheroni
--   limit, and `tendsto_nhds_unique` gives the required conditional uniqueness.
-- * Third-party search was not reached: the ordered search stopped at exact D5/Mathlib hits.

import D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Limits.EulerCountertermUniqueness

open Filter Topology
open scoped FourierTransform

-- The source's real Gaussian family under Mathlib's standard real Fourier convention.
noncomputable def standardGaussian (a : ℝ) : ℝ → ℂ :=
  fun x => (Real.exp (-a * x ^ 2) : ℂ)

-- The pointwise failure of the standard Gaussian at scale `a` to be Fourier self-dual.
noncomputable def gaussianSelfDualityDefect (a : ℝ) : ℝ → ℂ :=
  𝓕 (standardGaussian a) - standardGaussian a

-- A scale eliminates the Gaussian self-duality defect exactly when that defect is zero.
def EliminatesGaussianSelfDualityDefect (a : ℝ) : Prop :=
  gaussianSelfDualityDefect a = 0

-- The two source occurrences of conditional uniqueness, the concrete Euler-Mascheroni
-- existence certificate, and the source's Fourier-Gaussian contrast with pi.
theorem euler_counterterm_unique :
    (∀ c : ℝ,
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - c) atTop (𝓝 0) →
        c = Real.eulerMascheroniConstant) ∧
    Tendsto
      (fun n : ℕ =>
        (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)
      atTop (𝓝 0) ∧
    (∀ c : ℝ,
      Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - c) atTop (𝓝 0) →
        c = Real.eulerMascheroniConstant) ∧
    EliminatesGaussianSelfDualityDefect Real.pi := by
  have uniqueness :
      ∀ c : ℝ,
        Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - c) atTop (𝓝 0) →
          c = Real.eulerMascheroniConstant := by
    intro c residual_tendsto_zero
    have residual_tendsto_c :
        Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop (𝓝 c) := by
      convert residual_tendsto_zero.add_const c using 1 <;> simp
    exact tendsto_nhds_unique residual_tendsto_c Real.tendsto_harmonic_sub_log
  have existence :
      Tendsto
        (fun n : ℕ =>
          (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)
        atTop (𝓝 0) := by
    simpa only [sub_self] using
      Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
  have pi_eliminates : EliminatesGaussianSelfDualityDefect Real.pi := by
    have pi_self_dual :
        𝓕 (standardGaussian Real.pi) = standardGaussian Real.pi := by
      change
        𝓕 (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) =
          (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ))
      exact
        (D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi.gaussian_self_dual_iff
          Real.pi Real.pi_pos).2 rfl
    simp only [EliminatesGaussianSelfDualityDefect, gaussianSelfDualityDefect,
      pi_self_dual, sub_self]
  exact ⟨uniqueness, existence, uniqueness, pi_eliminates⟩

-- Reverse probe for CAS-A1: the first boxed occurrence remains independently projectable.
example (c : ℝ)
    (hc : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - c) atTop (𝓝 0)) :
    c = Real.eulerMascheroniConstant :=
  euler_counterterm_unique.1 c hc

-- Reverse probe for CAS-A2: gamma itself supplies the zero-residual certificate.
example :
    Tendsto
      (fun n : ℕ =>
        (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant)
      atTop (𝓝 0) :=
  euler_counterterm_unique.2.1

-- Reverse probe for CAS-A3: the second boxed uniqueness occurrence is separately projectable.
example (c : ℝ)
    (hc : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - c) atTop (𝓝 0)) :
    c = Real.eulerMascheroniConstant :=
  euler_counterterm_unique.2.2.1 c hc

-- Reverse probe for CAS-A4: pi eliminates the named Gaussian self-duality defect.
example : EliminatesGaussianSelfDualityDefect Real.pi :=
  euler_counterterm_unique.2.2.2

-- Trivialization probe for CAS-A2: zero cannot replace the concrete gamma witness.
example :
    ¬Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n - 0) atTop (𝓝 0) := by
  intro hzero
  have hpositive : (0 : ℝ) < Real.eulerMascheroniConstant :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  exact (ne_of_lt hpositive) (euler_counterterm_unique.1 0 hzero)

-- Collapse probe for CAS-A4: the elimination predicate distinguishes scale one from pi.
example : ¬EliminatesGaussianSelfDualityDefect 1 := by
  intro one_eliminates
  have one_self_dual : 𝓕 (standardGaussian 1) = standardGaussian 1 := by
    simpa only [EliminatesGaussianSelfDualityDefect, gaussianSelfDualityDefect,
      sub_eq_zero] using one_eliminates
  have one_eq_pi : (1 : ℝ) = Real.pi :=
    (D5.S3.Fourier.CompletionConstants.GaussianSelfDualPi.gaussian_self_dual_iff
      1 (by norm_num)).1 (by
        change
          𝓕 (fun x : ℝ => (Real.exp (-(1 : ℝ) * x ^ 2) : ℂ)) =
            (fun x : ℝ => (Real.exp (-(1 : ℝ) * x ^ 2) : ℂ)) at one_self_dual
        exact one_self_dual)
  linarith [Real.pi_gt_three]

#print axioms euler_counterterm_unique

end D5.S3.Constants.Limits.EulerCountertermUniqueness
