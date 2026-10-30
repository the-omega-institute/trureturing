/- GID: D5/S3/Analytic/Interpolation/SchurBoundaryKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurBoundaryKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.FunctionSeries, mathlib/module/Mathlib.Analysis.PSeries, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic]
   utility: none
   digest: The real Fourier kernel for an imaginary-axis divided difference. -/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Poisson

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Analytic.Interpolation.SchurBoundaryKernel

/-- The actual odd cosine series of the imaginary-axis primitive average. -/
def boundaryTerm (b θ : ℝ) (j : ℕ) : ℝ :=
  2 * ((-1 : ℝ) ^ (j + 1) * b ^ (2 * j + 2)) /
    ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3)) * Real.cos ((2 * (j : ℝ) + 1) * θ)

def boundaryKernel (b θ : ℝ) : ℝ := ∑' j : ℕ, boundaryTerm b θ j

private def majorant (j : ℕ) : ℝ :=
  2 / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))

private theorem majorant_summable : Summable majorant := by
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply Summable.of_nonneg_of_le (fun j => by dsimp [majorant]; positivity) _ hs
  intro j
  dsimp [majorant]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

private theorem term_norm_le {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (θ : ℝ) (j : ℕ) :
    ‖boundaryTerm b θ j‖ ≤ majorant j := by
  have hp : |b ^ (2 * j + 2)| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg hb.1]
    exact pow_le_one₀ hb.1 hb.2
  have hc := Real.abs_cos_le_one ((2 * (j : ℝ) + 1) * θ)
  rw [Real.norm_eq_abs]
  dsimp [boundaryTerm, majorant]
  rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < (2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))]
  calc
    _ ≤ (2 * 1 / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))) * 1 :=
      mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
        (by positivity)) hc (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem term_summable {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    Summable (boundaryTerm b θ) :=
  (majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_norm_le hb θ)).of_norm

private theorem kernel_continuous {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    Continuous (boundaryKernel b) := by
  exact continuous_tsum (fun j => by unfold boundaryTerm; fun_prop)
    majorant_summable (fun j θ => term_norm_le hb θ j)

private theorem kernel_uniform_convergence :
    TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => ∑ j ∈ Finset.range n, boundaryTerm p.1 p.2 j)
      (fun p => boundaryKernel p.1 p.2) atTop {p | p.1 ∈ Icc (0 : ℝ) 1} :=
  tendstoUniformlyOn_tsum_nat majorant_summable (fun j p hp => term_norm_le hp p.2 j)

private theorem kernel_reflection (b θ : ℝ) :
    boundaryKernel b (Real.pi - θ) = -boundaryKernel b θ := by
  unfold boundaryKernel
  rw [← tsum_neg]
  apply tsum_congr
  intro j
  have hc : Real.cos ((2 * (j : ℝ) + 1) * (Real.pi - θ)) =
      -Real.cos ((2 * (j : ℝ) + 1) * θ) := by
    have he : (2 * (j : ℝ) + 1) * (Real.pi - θ) =
        ((2 * j + 1 : ℕ) : ℝ) * Real.pi - (2 * (j : ℝ) + 1) * θ := by push_cast; ring
    rw [he, Real.cos_nat_mul_pi_sub]
    norm_num [pow_add, pow_mul]
  simp only [boundaryTerm, hc, mul_neg]

end D5.S3.Analytic.Interpolation.SchurBoundaryKernel
