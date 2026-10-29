/- GID: D5/S3/Analytic/Laplace/AbscissaSingularity
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/AbscissaSingularity
   mirror-E: none(waiver:analytic-proof-only)
   anchors: [D5/S3/Analytic/Laplace/NonnegativeContinuation]
   utility: none
   digest: The actual finite Laplace convergence cut of a nonnegative function is singular. -/

import D5.S3.Analytic.Laplace.NonnegativeContinuation

/-! Landau's positivity argument at the infimum of the actual convergence domain.
The measure is arbitrary; convergence and its order geometry are not assumed
beyond nonemptiness and boundedness below. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace D5.S3.Analytic.Laplace.AbscissaSingularity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- The actual real Laplace convergence domain, defined by integrability. -/
def convergenceSet (X : Ω → ℝ) (μ : Measure Ω) : Set ℝ :=
  {s | Integrable (fun ω => Real.exp (-s * X ω)) μ}

/-- No holomorphic function on a ball about the actual finite convergence cut
agrees with the original transform on the part of that ball to the right of the cut. -/
theorem no_holomorphic_extension_at_abscissa
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hne : (convergenceSet X μ).Nonempty) (hbdd : BddBelow (convergenceSet X μ))
    {R : ℝ} {H : ℂ → ℂ} (hR : 0 < R) :
    ¬ (DifferentiableOn ℂ H (Metric.ball ((sInf (convergenceSet X μ) : ℝ) : ℂ) R) ∧
      ∀ z ∈ Metric.ball ((sInf (convergenceSet X μ) : ℝ) : ℂ) R,
        sInf (convergenceSet X μ) < z.re → H z = complexMGF X μ (-z)) := by
  let σ := sInf (convergenceSet X μ)
  have hupper {s r : ℝ} (hs : s ∈ convergenceSet X μ) (hsr : s ≤ r) :
      r ∈ convergenceSet X μ := by
    apply hs.mono'
    · have hm : AEMeasurable (fun ω => Real.exp (-r * X ω)) μ := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [hX] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hsr) hω)
  have hcut {s : ℝ} (hs : s ∈ convergenceSet X μ) : σ ≤ s := csInf_le hbdd hs
  have hright : Ioi σ ⊆ convergenceSet X μ := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := exists_lt_of_csInf_lt hne hs
    exact hupper hr hrs.le
  have hinterior : Ioi σ ⊆ interior (convergenceSet X μ) := by
    simpa only [isOpen_Ioi.interior_eq] using interior_mono hright
  have hleft {s : ℝ} (hs : s < σ) : s ∉ convergenceSet X μ := by
    intro hi
    exact (not_le_of_gt hs) (hcut hi)
  -- Reflect an actual open subdomain, rather than a totalized integral value.
  have hreflect : Iio (-σ) ⊆ integrableExpSet X μ := by
    intro u hu
    have hi := interior_subset (hinterior (show -u ∈ Ioi σ by change σ < -u; change u < -σ at hu; linarith))
    simpa only [convergenceSet, mem_ofPred_eq, integrableExpSet, neg_neg] using hi
  let a := σ + R / 4
  have ha : -a ∈ interior (integrableExpSet X μ) := by
    have hi : -a ∈ Iio (-σ) := by dsimp [a]; simp only [mem_Iio]; linarith
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (isOpen_Iio.mem_nhds hi) hreflect)
  rintro ⟨hH, hagree⟩
  have hadist : dist (a : ℂ) (σ : ℂ) = R / 4 := by
    calc
      _ = |a - σ| := by simp [dist_eq_norm, ← Complex.ofReal_sub, Real.norm_eq_abs]
      _ = R / 4 := by
        rw [show a - σ = R / 4 by dsimp [a]; ring, abs_of_pos (by linarith : 0 < R / 4)]
  have hball : Metric.ball (a : ℂ) (3 * R / 4) ⊆ Metric.ball (σ : ℂ) R := by
    intro z hz
    calc
      dist z (σ : ℂ) ≤ dist z (a : ℂ) + dist (a : ℂ) (σ : ℂ) := dist_triangle _ _ _
      _ < 3 * R / 4 + R / 4 := by rw [hadist]; exact add_lt_add_right (Metric.mem_ball.mp hz) _
      _ = R := by ring
  have hHsmall : DifferentiableOn ℂ H (Metric.ball (a : ℂ) (3 * R / 4)) := hH.mono hball
  have hagerm : H =ᶠ[𝓝 (a : ℂ)] fun z => complexMGF X μ (-z) := by
    have haball : (a : ℂ) ∈ Metric.ball (σ : ℂ) R := by
      rw [Metric.mem_ball, hadist]
      linarith
    have haright : σ < (a : ℂ).re := by simp only [Complex.ofReal_re]; dsimp [a]; linarith
    filter_upwards [Metric.isOpen_ball.mem_nhds haball,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds haright] with z hz hzr
    exact hagree z hz hzr
  have hnew := NonnegativeContinuation.integrable_exp_of_laplace_extension
    hX ha hHsmall hagerm (t := R / 2) (by linarith) (by linarith)
  have hbelow : a - R / 2 < σ := by dsimp [a]; linarith
  apply hleft hbelow
  change Integrable (fun ω => Real.exp (-(a - R / 2) * X ω)) μ
  simpa only [neg_sub] using hnew.1

end D5.S3.Analytic.Laplace.AbscissaSingularity
