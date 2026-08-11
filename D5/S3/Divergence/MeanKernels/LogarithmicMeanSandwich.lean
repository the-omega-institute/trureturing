/- GID: D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich
   generality: G
   mirror-B: D5/B/S3/Divergence/MeanKernels/LogarithmicMeanSandwich
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The logarithmic-mean kernel is sandwiched between the arithmetic and harmonic reciprocal kernels: for positive reals a ≠ b, 2/(a+b) ≤ (log a − log b)/(a−b) ≤ (a⁻¹+b⁻¹)/2, equivalently the harmonic, logarithmic and arithmetic means satisfy H ≤ L ≤ A. -/

import Mathlib

namespace D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich

open Real

/-- Scalar left bound: `2·(t−1)/(t+1) ≤ log t` for `t ≥ 1`, proved by monotonicity of
`s ↦ log s − 2·(s−1)/(s+1)` on `[1,∞)` (its derivative `(s−1)²/(s(s+1)²)` is nonnegative). -/
private theorem two_mul_sub_div_add_le_log {t : ℝ} (ht : 1 ≤ t) :
    2 * ((t - 1) / (t + 1)) ≤ Real.log t := by
  have hderiv : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun s : ℝ => Real.log s - 2 * ((s - 1) / (s + 1)))
        ((s - 1) ^ 2 / (s * (s + 1) ^ 2)) s := by
    intro s hs0
    have hs1' : s + 1 ≠ 0 := by positivity
    have hlog := Real.hasDerivAt_log (ne_of_gt hs0)
    have hnum : HasDerivAt (fun s : ℝ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have hden : HasDerivAt (fun s : ℝ => s + 1) 1 s := (hasDerivAt_id s).add_const 1
    have hdiv : HasDerivAt (fun s : ℝ => (s - 1) / (s + 1))
        ((1 * (s + 1) - (s - 1) * 1) / (s + 1) ^ 2) s := hnum.div hden hs1'
    have hcm : HasDerivAt (fun s : ℝ => 2 * ((s - 1) / (s + 1)))
        (2 * ((1 * (s + 1) - (s - 1) * 1) / (s + 1) ^ 2)) s := hdiv.const_mul 2
    have hsub := hlog.sub hcm
    have heq : s⁻¹ - 2 * ((1 * (s + 1) - (s - 1) * 1) / (s + 1) ^ 2)
        = (s - 1) ^ 2 / (s * (s + 1) ^ 2) := by field_simp; ring
    rw [← heq]; exact hsub
  have mono : MonotoneOn (fun s : ℝ => Real.log s - 2 * ((s - 1) / (s + 1))) (Set.Ici (1 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · apply ContinuousOn.sub
      · exact Real.continuousOn_log.mono (fun s hs => by
          simp only [Set.mem_Ici] at hs; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h; rw [h] at hs; linarith)
      · apply ContinuousOn.const_mul
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro s hs; simp only [Set.mem_Ici] at hs; positivity
    · rw [interior_Ici]; intro s hs; simp only [Set.mem_Ioi] at hs
      exact (hderiv s (lt_trans one_pos hs)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]; intro s hs; simp only [Set.mem_Ioi] at hs
      rw [(hderiv s (lt_trans one_pos hs)).deriv]; positivity
  have hkey := mono Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  norm_num at hkey; linarith

/-- Scalar right bound: `log t ≤ (t − 1/t)/2` for `t ≥ 1`, from `x ≤ sinh x` at `x = log t ≥ 0`. -/
private theorem log_le_sub_inv_div_two {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ (t - 1 / t) / 2 := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have key : Real.log t ≤ Real.sinh (Real.log t) := (Real.self_le_sinh_iff).mpr (Real.log_nonneg ht)
  have hsinh : Real.sinh (Real.log t) = (t - 1 / t) / 2 := by
    rw [Real.sinh_eq, Real.exp_log htpos, Real.exp_neg, Real.exp_log htpos]; ring
  rwa [hsinh] at key

/-- Ordered kernel sandwich for `b < a` (both positive). -/
private theorem sandwich_ordered {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    2 / (a + b) ≤ (Real.log a - Real.log b) / (a - b) ∧
      (Real.log a - Real.log b) / (a - b) ≤ (a⁻¹ + b⁻¹) / 2 := by
  have ha : 0 < a := lt_trans hb hab
  have hsub : 0 < a - b := sub_pos.mpr hab
  have hab' : 0 < a + b := by positivity
  have ht : 1 ≤ a / b := (one_le_div hb).mpr (le_of_lt hab)
  have hlogdiv : Real.log a - Real.log b = Real.log (a / b) :=
    (Real.log_div (ne_of_gt ha) (ne_of_gt hb)).symm
  refine ⟨?_, ?_⟩
  · rw [hlogdiv, div_le_div_iff₀ hab' hsub]
    have hA := two_mul_sub_div_add_le_log ht
    have hrw : (a / b - 1) / (a / b + 1) = (a - b) / (a + b) := by field_simp
    rw [hrw] at hA
    have h3 : 2 * (a - b) / (a + b) ≤ Real.log (a / b) := by rw [mul_div_assoc]; exact hA
    rw [div_le_iff₀ hab'] at h3; linarith [h3]
  · rw [hlogdiv, div_le_div_iff₀ hsub (by positivity)]
    have hB := log_le_sub_inv_div_two ht
    have hrw : (a / b - 1 / (a / b)) / 2 = (a ^ 2 - b ^ 2) / (2 * a * b) := by field_simp
    rw [hrw] at hB
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a * b)] at hB
    have hgoal : (a⁻¹ + b⁻¹) * (a - b) = (a ^ 2 - b ^ 2) / (a * b) := by field_simp; ring
    rw [hgoal, le_div_iff₀ (by positivity : (0 : ℝ) < a * b)]
    nlinarith [hB]

/-- The logarithmic-mean kernel sandwich. For positive reals `a ≠ b`, the reciprocal kernel of the
logarithmic mean lies between the reciprocal kernels of the arithmetic and harmonic means:
`2/(a+b) ≤ (log a − log b)/(a−b) ≤ (a⁻¹+b⁻¹)/2`. Taking reciprocals, this is the classical chain
`H(a,b) ≤ L(a,b) ≤ A(a,b)` of harmonic, logarithmic and arithmetic means. -/
theorem logMean_kernel_sandwich {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    2 / (a + b) ≤ (Real.log a - Real.log b) / (a - b) ∧
      (Real.log a - Real.log b) / (a - b) ≤ (a⁻¹ + b⁻¹) / 2 := by
  rcases lt_or_gt_of_ne hne with h | h
  · have H := sandwich_ordered ha h
    have esym : (Real.log a - Real.log b) / (a - b) = (Real.log b - Real.log a) / (b - a) := by
      rw [show Real.log a - Real.log b = -(Real.log b - Real.log a) from by ring,
          show a - b = -(b - a) from by ring, neg_div_neg_eq]
    rw [esym, show a + b = b + a from by ring, show a⁻¹ + b⁻¹ = b⁻¹ + a⁻¹ from by ring]
    exact H
  · exact sandwich_ordered hb h

end D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich
