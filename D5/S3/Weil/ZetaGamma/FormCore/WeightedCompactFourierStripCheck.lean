import D5.S3.Weil.ZetaCore.PaperFT

/- Source draft for the noncompact explicit-formula extension. Not compiled.
   The single new statement is the support-radius-independent estimate used
   by k_R = chi_R * k. In particular, do not replace the weighted integral by
   exp(R/2) times an unweighted norm: that loses uniformity as R tends to infinity.

   Repository search: ZetaCore/PaperFT and ExplicitFormulaBridge provide the
   compact-support-radius bounds; no weighted strip version was found in
   D5/S3/Weil or D5/S3/Analytic/Fourier. Reuses paperFT_deriv_deriv verbatim.
   Proposed CLAUDE 3.2 proof_shape: content, from the new pointwise strip
   exponential majorant through the zeroth/second-order integral estimates.
   Actual consumer: the uniform Fourier envelope for the C2 cutoffs k_R.
-/

namespace Zeta23

open Complex MeasureTheory Real Set Filter Topology

/-- A support-radius-independent half-strip envelope. The weighted zeroth
    and second derivatives pay for the entire closed strip, including z=0. -/
theorem norm_paperFT_weighted_strip_le {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    (1 + ‖z‖ ^ 2) * ‖paperFT f z‖ ≤
      ∫ u : ℝ, (‖f u‖ + ‖deriv (deriv f) u‖) * Real.exp (|u| / 2) := by
  have hw (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun u : ℝ => ‖g u‖ * Real.exp (|u| / 2)) :=
    (hg.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.norm.mul_right
  have hbound (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      ‖paperFT g z‖ ≤ ∫ u : ℝ, ‖g u‖ * Real.exp (|u| / 2) := by
    rw [paperFT_def]
    apply norm_integral_le_of_norm_le (hw g hg hgc)
      (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_cexp_I_mul]
    apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    calc
      -(z.im * u) ≤ |z.im * u| := neg_le_abs _
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ (1 / 2) * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      _ = |u| / 2 := by ring
  have hfdc : Continuous (deriv (deriv f)) :=
    (hf.deriv').continuous_deriv le_rfl
  calc
    (1 + ‖z‖ ^ 2) * ‖paperFT f z‖ =
        ‖paperFT f z‖ + ‖paperFT (deriv (deriv f)) z‖ := by
      rw [paperFT_deriv_deriv hf hfc, norm_mul, norm_neg, norm_pow]
      ring
    _ ≤ (∫ u : ℝ, ‖f u‖ * Real.exp (|u| / 2)) +
        ∫ u : ℝ, ‖deriv (deriv f) u‖ * Real.exp (|u| / 2) :=
      add_le_add (hbound f hf.continuous hfc)
        (hbound (deriv (deriv f)) hfdc hfc.deriv.deriv)
    _ = _ := by
      rw [← integral_add (hw f hf.continuous hfc)
        (hw (deriv (deriv f)) hfdc hfc.deriv.deriv)]
      congr 1
      ext u
      ring

end Zeta23

#print axioms Zeta23.norm_paperFT_weighted_strip_le
