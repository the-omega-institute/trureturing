/- GID: D5/S3/Weil/Mertens/ActualPsiTailEulerBridge
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/ActualPsiTailEulerBridge
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Actual psi-tail continuation and Euler forcing. -/

import D5.S3.Analytic.Laplace.ActivationTailEuler
import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Weil.Mertens.PsiLaplaceForcing

/-! The actual signed psi tail satisfies its Euler equation on Re s > 0. -/

noncomputable section
open Real Set MeasureTheory Filter Complex
open scoped Topology

namespace D5.S3.Weil.Mertens.PsiLaplaceForcing

open PsiLaplaceContinuation
open D5.S3.Analytic.Laplace.EulerPoleObstruction

/-- The actual L1 tail, its transform and both derivatives, and the forcing
with the positive cutoff boundary, uniformly in every U >= log 2. -/
theorem actual_tail_bridge :
    IntegrableOn fpsi (Ioi (Real.log 2)) ∧
    ∀ U : ℝ, Real.log 2 ≤ U →
      AnalyticOnNhd ℂ (tailLaplace fpsi U) {z | 0 < z.re} ∧
      ∀ z : ℂ, 0 < z.re →
        (∀ n : ℕ, IntegrableOn (fun u : ℝ =>
          (u : ℂ) ^ n * Complex.exp (-z * (u : ℂ)) * (fpsi u : ℂ)) (Ioi U)) ∧
        HasDerivAt (tailLaplace fpsi U)
          (-(∫ u in Ioi U, (u : ℂ) * Complex.exp (-z * (u : ℂ)) * (fpsi u : ℂ))) z ∧
        HasDerivAt (deriv (tailLaplace fpsi U))
          (∫ u in Ioi U, (u : ℂ) ^ 2 * Complex.exp (-z * (u : ℂ)) * (fpsi u : ℂ)) z ∧
        euler (tailLaplace fpsi U) z = Phi U z := by
  have hf : fpsi = D5.S3.Analytic.Laplace.ActivationTailEuler.f qpsi := by
    funext u
    exact fpsi_eq_tail u
  have hL (U : ℝ) : tailLaplace fpsi U =
      D5.S3.Analytic.Laplace.ActivationTailEuler.L qpsi U := by
    rw [hf]
    rfl
  obtain ⟨_, hfi, _, _, _, _, hcut⟩ :=
    D5.S3.Analytic.Laplace.ActivationTailEuler.actual_tail_laplace_ode
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)) qpsi_measurable qpsi_integrable
  refine ⟨by simpa only [← hf] using hfi, ?_⟩
  intro U hU
  obtain ⟨hLa, _, hdata⟩ := hcut U hU
  refine ⟨by simpa only [← hL U] using hLa, ?_⟩
  intro z hz
  obtain ⟨hn, hd, hdd, _, _, _, heuler⟩ := hdata z hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [← hf] using hn
  · simpa only [← hL U, ← hf] using hd
  · simpa only [← hL U, ← hf] using hdd
  · have hQM : Qpsi U =ᶠ[𝓝 z] Mpsi U := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz]
        with w hw using Qpsi_eq_Mpsi U hw
    have he : euler (tailLaplace fpsi U) z =
        -deriv (Qpsi U) z + Qpsi U z + boundary U z := by
      rw [hL U]
      have hQ : D5.S3.Analytic.Laplace.ActivationTailEuler.Q qpsi U = Qpsi U := rfl
      rw [hQ] at heuler
      simpa only [euler, boundary, ← hf] using heuler
    rw [hQM.deriv_eq, hQM.eq_of_nhds] at he
    exact he

-- The delivered signed_peaks API consumes actual_tail_bridge at U = log 2.
-- No obsolete EulerTail structure or named signed-peak wrapper is proposed.

end D5.S3.Weil.Mertens.PsiLaplaceForcing
