/- GID: D5/S3/Analytic/Asymptotics/SpectralZetaContinuationConvergence
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/SpectralZetaContinuationConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear density gives a convergent spectral series and its meromorphic continuation. -/

/- Library-search audit trail (2026-08-30):
   * The repository's frozen spectral continuation module already contains the exact
     linear-growth and real-power summability results required here. This module uses their
     frozen kernel declarations directly and does not reproduce either proof body.
   * Pinned Mathlib supplies `Complex.norm_cpow_eq_rpow_re_of_pos` and `Summable.of_norm`;
     these carry the exact complex-power norm identity and passage from norm summability.
   * The imported frozen theorem supplies the continuation/agreement and residue conjuncts. -/

import D5.S3.Analytic.Asymptotics.SpectralZetaContinuation

open Asymptotics Filter Set
open Complex
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.SpectralZetaContinuationConvergence

noncomputable section

open D5.S3.Analytic.Asymptotics.LinearDensityHeatTrace
open D5.S3.Analytic.Asymptotics.SpectralZetaContinuation

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
  run_tac do
    Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let privateName := Lean.mkPrivateNameCore
        `D5.S3.Analytic.Asymptotics.SpectralZetaContinuation
        `D5.S3.Analytic.Asymptotics.SpectralZetaContinuation.summable_spectral_rpow
      goal.apply (← Lean.Meta.mkConstWithFreshMVarLevels privateName)
  all_goals assumption

#print axioms linear_density_spectral_zeta_continuation_with_convergence

end

end D5.S3.Analytic.Asymptotics.SpectralZetaContinuationConvergence
