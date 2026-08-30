/- GID: D5/S3/Analytic/Asymptotics/SpectralZetaContinuationConvergence
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/SpectralZetaContinuationConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear density gives a convergent spectral series and its meromorphic continuation. -/

/- Library-search audit trail (2026-08-30):
   * Repository searches found the frozen continuation theorem and its exact spectral-series
     definitions, but its convergence helpers are private and no public theorem exports
     summability of the complex Dirichlet terms.
   * Pinned Mathlib supplies `Real.summable_nat_rpow`,
     `Complex.norm_cpow_eq_rpow_re_of_pos`, and `Summable.of_norm`; these carry the comparison,
     the exact complex-power norm identity, and the passage from norm summability.
   * The imported frozen theorem supplies the continuation/agreement and residue conjuncts
     directly. This module redeclares none of the spectral family types or definitions. -/

import D5.S3.Analytic.Asymptotics.SpectralZetaContinuation

open Asymptotics Filter Set
open Complex
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.SpectralZetaContinuationConvergence

noncomputable section

open D5.S3.Analytic.Asymptotics.LinearDensityHeatTrace
open D5.S3.Analytic.Asymptotics.SpectralZetaContinuation

private lemma eventually_linear_lower (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / (2 * (|c| + 1)) ≤ lambda n := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hdensity
  simp only [norm_one, mul_one] at hC
  obtain ⟨U, hU⟩ := eventually_atTop.1 hC
  have houtside : ∀ᶠ n : ℕ in atTop, n ∉ {n | lambda n ≤ U} := by
    rw [← Nat.cofinite_eq_atTop]
    exact (hfinite U).eventually_cofinite_notMem
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 * C ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 * C))
  filter_upwards [houtside, hnlarge] with n hnU hnC
  have hUn : U ≤ lambda n := le_of_not_ge hnU
  have hbound := hU (lambda n) hUn
  have hcount : spectralCounting lambda (lambda n) = (n : ℝ) + 1 := by
    have hset : {k | lambda k ≤ lambda n} = Set.Iic n := by
      ext k
      exact hstrict.le_iff_le
    unfold spectralCounting
    rw [hset, Set.ncard_Iic_nat]
    norm_num
  have hupper : (n : ℝ) + 1 ≤ |c| * lambda n + C := by
    calc
      (n : ℝ) + 1 = spectralCounting lambda (lambda n) := hcount.symm
      _ ≤ c * lambda n + C := by
        have hresidual : spectralCounting lambda (lambda n) - c * lambda n ≤ C :=
          (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound)
        linarith
      _ ≤ |c| * lambda n + C := by
        simpa only [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_right (le_abs_self c) (hpos n).le) C
  have hlinear : (n : ℝ) / 2 ≤ (|c| + 1) * lambda n := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlambda := (hpos n).le
    nlinarith [abs_nonneg c]
  rw [div_le_iff₀ (by positivity : 0 < 2 * (|c| + 1))]
  nlinarith

private lemma summable_spectral_rpow (lambda : ℕ → ℝ) (c r : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) (hr : 1 < r) :
    Summable (fun n : ℕ => 1 / lambda n ^ r) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-r)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => (2 * (|c| + 1)) ^ r * (n : ℝ) ^ (-r))
    (hbase.mul_left _) ?_
  filter_upwards [eventually_linear_lower lambda c hpos hstrict hfinite hdensity,
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn hnpos
  rw [Real.norm_eq_abs, abs_of_pos
    (div_pos one_pos (Real.rpow_pos_of_pos (hpos n) r))]
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hdenom : 0 < 2 * (|c| + 1) := by positivity
  calc
    1 / lambda n ^ r = lambda n ^ (-r) := by
      simpa only [one_div] using (Real.rpow_neg (hpos n).le r).symm
    _ ≤ ((n : ℝ) / (2 * (|c| + 1))) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hn (by linarith)
    _ = (2 * (|c| + 1)) ^ r * (n : ℝ) ^ (-r) := by
      rw [Real.div_rpow hnreal.le hdenom.le, Real.rpow_neg hnreal.le,
        Real.rpow_neg hdenom.le]
      field_simp

/-- Linear spectral density publicly supplies all three source clauses: the named meromorphic
continuation agrees with the spectral Dirichlet series on its initial half-plane, that exact
complex series is summable there, and the continuation has residue `c` at one. -/
theorem linear_density_spectral_zeta_continuation_with_convergence (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    IsSpectralZetaContinuation lambda (continuedSpectralZeta lambda c) ∧
      (∀ s : ℂ, 1 < s.re → Summable (fun n : ℕ => (lambda n : ℂ) ^ (-s))) ∧
      Tendsto (fun s : ℂ => (s - 1) * continuedSpectralZeta lambda c s)
        (𝓝[≠] 1) (𝓝 (c : ℂ)) := by
  have hfrozen := linear_density_spectral_zeta_continuation
    lambda c hpos hstrict hfinite hdensity
  refine ⟨hfrozen.1, ?_, hfrozen.2⟩
  intro s hs
  apply Summable.of_norm
  rw [show (fun n : ℕ => ‖(lambda n : ℂ) ^ (-s)‖) =
      fun n : ℕ => 1 / lambda n ^ s.re by
    funext n
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos n) (-s), neg_re,
      Real.rpow_neg (hpos n).le]
    simp only [one_div]]
  exact summable_spectral_rpow lambda c s.re hpos hstrict hfinite hdensity hs

#print axioms linear_density_spectral_zeta_continuation_with_convergence

end

end D5.S3.Analytic.Asymptotics.SpectralZetaContinuationConvergence
