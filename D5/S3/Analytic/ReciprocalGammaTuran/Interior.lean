/- GID: D5/S3/Analytic/ReciprocalGammaTuran/Interior
   generality: G
   mirror-B: D5/B/S3/Analytic/ReciprocalGammaTuran/Interior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint continuity of reciprocal Gamma coefficients and strictly interior failures of coefficient positivity. -/

import D5.S3.Analytic.ReciprocalGammaTuran.Boundary

open D5.S3.Analytic.ReciprocalGammaTuran.Defs
open D5.S3.Analytic.ReciprocalGammaTuran.Boundary
open Filter Set
open scoped Topology
namespace D5.S3.Analytic.ReciprocalGammaTuran.Interior

private lemma continuous_rgamma : Continuous rgamma := by
  have h := Complex.differentiable_one_div_Gamma.continuous
  have he : rgamma = fun x : ℝ => ((Complex.Gamma (x : ℂ))⁻¹).re := by
    funext x
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]
    rfl
  rw [he]
  exact Complex.continuous_re.comp (h.comp Complex.continuous_ofReal)

/-- Every finite Turanian coefficient is continuous in the three shifts. -/
theorem continuous_turanCoeff_two :
    Continuous (fun p : ℝ × ℝ × ℝ => turanCoeff (fun _ => 1) p.1 p.2.1 p.2.2 2) := by
  unfold turanCoeff
  apply continuous_finsetSum
  intro k hk
  apply Continuous.mul continuous_const
  apply Continuous.sub
  · apply Continuous.mul
    · exact continuous_rgamma.comp (by fun_prop)
    · exact continuous_rgamma.comp (by fun_prop)
  · apply Continuous.mul
    · exact continuous_rgamma.comp (by fun_prop)
    · exact continuous_rgamma.comp (by fun_prop)

/-- Strict coefficient negativity persists at strictly interior parameters. -/
theorem interior_failure : ∃ μ α β : ℝ,
    0 < μ + α ∧ 0 < μ + β ∧ 0 < α ∧ 0 < β ∧ -1 ≤ μ ∧
      turanCoeff (fun _ => 1) μ α β 2 < 0 := by
  have hc : Continuous (fun ε : ℝ =>
      turanCoeff (fun _ => 1) (-(1 / 2) + ε) (1 / 2) (1 / 2) 2) :=
    continuous_turanCoeff_two.comp (f := fun ε : ℝ =>
      (-(1 / 2) + ε, (1 / 2, 1 / 2))) (by fun_prop)
  have hneg : ∀ᶠ ε : ℝ in 𝓝 0,
      turanCoeff (fun _ => 1) (-(1 / 2) + ε) (1 / 2) (1 / 2) 2 < 0 := by
    exact (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using d_two_half_neg))
  obtain ⟨δ, hδ, hcoef⟩ := Metric.eventually_nhds_iff.mp hneg
  refine ⟨-(1 / 2) + δ / 2, 1 / 2, 1 / 2, ?_, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · apply hcoef
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
end D5.S3.Analytic.ReciprocalGammaTuran.Interior
