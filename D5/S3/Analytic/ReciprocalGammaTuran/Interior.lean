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

/-- The second Turanian coefficient is continuous in the three shifts. -/
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

private lemma interior_negative_interval {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      0 < (-t + ε) + t ∧ -1 ≤ -t + ε ∧
        turanCoeff (fun _ => 1) (-t + ε) t t 2 < 0 := by
  have hc : Continuous (fun ε : ℝ => turanCoeff (fun _ => 1) (-t + ε) t t 2) :=
    continuous_turanCoeff_two.comp (f := fun ε : ℝ => (-t + ε, (t, t))) (by fun_prop)
  have hneg : ∀ᶠ ε : ℝ in 𝓝 0, turanCoeff (fun _ => 1) (-t + ε) t t 2 < 0 :=
    (hc.tendsto 0).eventually (gt_mem_nhds (by simpa using d_two_neg ht ht1))
  obtain ⟨δ, hδ, hcoef⟩ := Metric.eventually_nhds_iff.mp hneg
  refine ⟨δ, hδ, fun ε hε hεδ => ⟨by linarith, by linarith, ?_⟩⟩
  apply hcoef
  simpa [Real.dist_eq, abs_of_pos hε] using hεδ

/-- Strict coefficient negativity persists at strictly interior parameters. -/
theorem interior_failure : ∃ μ α β : ℝ,
    0 < μ + α ∧ 0 < μ + β ∧ 0 < α ∧ 0 < β ∧ -1 ≤ μ ∧
      turanCoeff (fun _ => 1) μ α β 2 < 0 := by
  obtain ⟨δ, hδ, H⟩ := interior_negative_interval (t := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨hshift, hμ, hneg⟩ := H (δ / 2) (by linarith) (by linarith)
  exact ⟨-(1 / 2) + δ / 2, 1 / 2, 1 / 2, hshift, hshift,
    by norm_num, by norm_num, hμ, hneg⟩
end D5.S3.Analytic.ReciprocalGammaTuran.Interior
