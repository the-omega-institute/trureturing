/- GID: D5/S3/Analytic/Interpolation/SchurConjugateSlope
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurConjugateSlope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.CauchyIntegral, mathlib/module/Mathlib.Analysis.Complex.RealDeriv, mathlib/module/Mathlib.Analysis.Calculus.MeanValue]
   utility: none
   digest: Horizontal transport of an actual entire-function conjugate-pair slope. -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Metric Complex

namespace D5.S3.Analytic.Interpolation.SchurConjugateSlope

/-- The original closed-disk second-derivative norm, without coefficient restrictions. -/
def diskNorm (g : ℂ → ℂ) : ℝ :=
  sSup ((fun z => ‖deriv (deriv g) z‖) '' closedBall (0 : ℂ) 1)

/-- The divided difference at the two actual nodes. -/
def slope (g : ℂ → ℂ) (a b : ℝ) : ℂ :=
  (g ((a : ℂ) + b * I) - g ((a : ℂ) - b * I)) / (2 * b * I)

/-- The original two-node Lagrange expression. -/
def interpolant (g : ℂ → ℂ) (a b : ℝ) (z : ℂ) : ℂ :=
  (z - ((a : ℂ) - b * I)) / (2 * b * I) * g ((a : ℂ) + b * I) +
    (((a : ℂ) + b * I) - z) / (2 * b * I) * g ((a : ℂ) - b * I)

private theorem diskNorm_bdd (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    BddAbove ((fun z => ‖deriv (deriv g) z‖) '' closedBall (0 : ℂ) 1) :=
  (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hg.deriv.deriv.continuous.norm.continuousOn

private theorem le_diskNorm {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : ‖deriv (deriv g) z‖ ≤ diskNorm g :=
  le_csSup (diskNorm_bdd g hg) ⟨z, hz, rfl⟩

private theorem node_mem {a b s : ℝ} (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hs : |s| ≤ |a|) : (s : ℂ) + b * I ∈ closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right]
  have hn : ‖(s : ℂ) + b * I‖ ^ 2 = s ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
  have hsa : s ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs s, sq_abs a]
  nlinarith [norm_nonneg ((s : ℂ) + b * I)]

private theorem slope_hasDeriv {g : ℂ → ℂ} (hg : Differentiable ℂ g) (b : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (g (z + b * I) - g (z - b * I)) / (2 * b * I))
      ((deriv g (s + b * I) - deriv g (s - b * I)) / (2 * b * I)) s := by
  simpa using (((hg (s + b * I)).hasDerivAt.comp s ((hasDerivAt_id s).add_const (b * I))).sub
    ((hg (s - b * I)).hasDerivAt.comp s ((hasDerivAt_id s).sub_const (b * I)))).div_const
      (2 * b * I)

/-- The actual Lagrange derivative is the original slope at every complex test point. -/
theorem interpolant_deriv (g : ℂ → ℂ) (a b : ℝ) (z : ℂ) :
    deriv (interpolant g a b) z = slope g a b := by
  have h := ((((hasDerivAt_id z).sub_const ((a : ℂ) - b * I)).div_const
    (2 * b * I)).mul_const (g ((a : ℂ) + b * I))).add
      ((((hasDerivAt_const z ((a : ℂ) + b * I)).sub (hasDerivAt_id z)).div_const
        (2 * b * I)).mul_const (g ((a : ℂ) - b * I)))
  convert h.deriv using 1 <;> dsimp [interpolant, slope] <;> ring

/-- Horizontal displacement on the full admissible closed disk, for every entire function. -/
theorem slope_transport (g : ℂ → ℂ) (hg : Differentiable ℂ g) (a b : ℝ)
    (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    ‖slope g a b - slope g 0 b‖ ≤ |a| * diskNorm g := by
  have hden : (2 * (b : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hb.ne')) I_ne_zero
  let f : ℝ → ℂ := fun s => slope g s b
  let f' : ℝ → ℂ := fun s =>
    (deriv g ((s : ℂ) + b * I) - deriv g ((s : ℂ) - b * I)) / (2 * b * I)
  have hf (s : ℝ) : HasDerivAt f (f' s) s := (slope_hasDeriv hg b s).comp_ofReal
  have hbound (s : ℝ) (hs : s ∈ Icc (-|a|) |a|) : ‖f' s‖ ≤ diskNorm g := by
    have hs' : |s| ≤ |a| := abs_le.mpr hs
    have hu := node_mem hab hs'
    have hv : (s : ℂ) - b * I ∈ closedBall (0 : ℂ) 1 := by
      have hh := node_mem (b := -b) (by nlinarith : a ^ 2 + (-b) ^ 2 ≤ 1) hs'
      simpa using hh
    have hh := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hg.deriv z) (fun z hz => le_diskNorm hg hz) hv hu
    have he : ((s : ℂ) + b * I) - ((s : ℂ) - b * I) = 2 * b * I := by ring
    rw [he] at hh
    dsimp [f']
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hden)).mpr hh
  have hh := (convex_Icc (-|a|) |a|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hf s).hasDerivWithinAt) hbound
    (show (0 : ℝ) ∈ Icc (-|a|) |a| by constructor <;> linarith [abs_nonneg a])
    (show a ∈ Icc (-|a|) |a| from ⟨neg_abs_le a, le_abs_self a⟩)
  simpa only [f, sub_zero, Real.norm_eq_abs, mul_comm] using hh

/-- The horizontal transport estimate for the derivatives of the actual interpolants. -/
theorem interpolant_transport (g : ℂ → ℂ) (hg : Differentiable ℂ g) (a b : ℝ)
    (hb : 0 < b) (hab : a ^ 2 + b ^ 2 ≤ 1) (z : ℂ) :
    ‖deriv (interpolant g a b) z - deriv (interpolant g 0 b) z‖ ≤ |a| * diskNorm g := by
  simpa only [interpolant_deriv] using slope_transport g hg a b hb hab

#print axioms slope_transport
#print axioms interpolant_deriv

end D5.S3.Analytic.Interpolation.SchurConjugateSlope
