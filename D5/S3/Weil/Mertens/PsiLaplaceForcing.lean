/- GID: D5/S3/Weil/Mertens/PsiLaplaceForcing
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/PsiLaplaceForcing
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Actual psi-tail continuation and Euler forcing. -/

import D5.S3.Weil.Mertens.PsiLaplaceContinuation
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope

/-! The signed psi tail and its meromorphic Euler forcing with the positive cutoff boundary. -/

namespace D5.S3.Weil.Mertens.PsiLaplaceForcing

open Real Set MeasureTheory Filter Complex
open scoped Topology
open PsiLaplaceContinuation

noncomputable section

/-- The actual signed psi tail in the existing arithmetic envelope. -/
def fpsi (u : ℝ) : ℝ :=
  -D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.Jpsi (Real.exp u)

/-- The same activation weight as the original actual theta tail. -/
def kpsi (u : ℝ) : ℝ := qpsi u * (u + 1) / u ^ 2

private theorem exp_activation (u : ℝ) :
    Real.exp u * ((Chebyshev.psi (Real.exp u) - Real.exp u) *
      D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity (Real.exp u)) =
      kpsi u := by
  dsimp [D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity, kpsi, qpsi]
  rw [Real.log_exp, Real.exp_neg]
  field_simp

/-- Identification of the actual tail only; no differentiability is inferred. -/
theorem fpsi_eq_tail (u : ℝ) : fpsi u = -(∫ v in Ioi u, kpsi v) := by
  unfold fpsi D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.Jpsi
    D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.w
  congr 1
  have h := integral_comp_exp_Ioi (fun t : ℝ => (Chebyshev.psi t - t) *
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity t) u
  simpa only [smul_eq_mul, exp_activation] using h.symm

def boundary (U : ℝ) (s : ℂ) : ℂ :=
  (U : ℂ) ^ 2 * (fpsi U : ℂ) * Complex.exp (-s * (U : ℂ))

/-- The meromorphic Euler forcing, including the positive cutoff boundary. -/
def Phi (U : ℝ) (s : ℂ) : ℂ :=
  -deriv (Mpsi U) s + Mpsi U s + boundary U s

theorem boundary_analytic (U : ℝ) (s : ℂ) : AnalyticAt ℂ (boundary U) s := by
  unfold boundary
  fun_prop

/-- All cutoffs have exactly the same complete double-pole coefficient.
The normalized limit is taken in the full complex punctured neighbourhood.
This assertion makes no claim about convergence of actual integrals for Re s < 0. -/
theorem actual_forcing_poles (U : ℝ) {ρ : ℂ} (hρ : D5.S3.Weil.ZeroSum.IsNontrivialZero ρ) :
    let a := ρ - 1
    let m := analyticOrderNatAt riemannZeta ρ
    let Λ := -(m : ℂ) / ρ
    a ∈ Dpsi ∧ a ≠ 0 ∧ a.im ≠ 0 ∧ 0 < m ∧ Λ ≠ 0 ∧
    meromorphicOrderAt (Mpsi U) a = (-1 : ℤ) ∧
    meromorphicOrderAt (Phi U) a = (-2 : ℤ) ∧
    Tendsto (fun s : ℂ => (s - a) * Mpsi U s) (𝓝[≠] a) (𝓝 Λ) ∧
    Tendsto (fun s : ℂ => (s - a) ^ 2 * Phi U s) (𝓝[≠] a) (𝓝 Λ) ∧
    ∃ J : ℂ → ℂ, AnalyticAt ℂ J a ∧
      Phi U =ᶠ[𝓝[≠] a] (fun s => Λ / (s - a) ^ 2 + Λ / (s - a) + J s) := by
  let a := ρ - 1
  let m := analyticOrderNatAt riemannZeta ρ
  let Λ := -(m : ℂ) / ρ
  obtain ⟨haD, ha0, him, hm, _, hΛ, H, hH, _, hexp, hMorder, hPorder⟩ :=
    actual_source_poles U hρ
  let J : ℂ → ℂ := fun s => H s - deriv H s + boundary U s
  have hJ : AnalyticAt ℂ J a := (hH.sub hH.deriv).add (boundary_analytic U a)
  have hPhi : Phi U =ᶠ[𝓝[≠] a]
      (fun s => Λ / (s - a) ^ 2 + Λ / (s - a) + J s) := by
    filter_upwards [hexp] with s hs
    change -deriv (Mpsi U) s + Mpsi U s =
      Λ / (s - a) ^ 2 + Λ / (s - a) + H s - deriv H s at hs
    change (-deriv (Mpsi U) s + Mpsi U s) + boundary U s = _
    rw [hs]
    dsimp [J]
    ring
  have hlt : meromorphicOrderAt (fun s => -deriv (Mpsi U) s + Mpsi U s) a <
      meromorphicOrderAt (boundary U) a := by
    rw [hPorder]
    exact lt_of_lt_of_le (by exact_mod_cast (show (-2 : ℤ) < 0 by norm_num))
      (boundary_analytic U a).meromorphicOrderAt_nonneg
  have horder : meromorphicOrderAt (Phi U) a = (-2 : ℤ) := by
    change meromorphicOrderAt ((fun s => -deriv (Mpsi U) s + Mpsi U s) + boundary U) a = _
    rw [meromorphicOrderAt_add_eq_left_of_lt (boundary_analytic U a).meromorphicAt hlt,
      hPorder]
  have hc : ContinuousAt (fun s : ℂ => Λ + Λ * (s - a) + (s - a) ^ 2 * J s) a := by
    have hj := hJ.continuousAt
    fun_prop
  have hp : Tendsto (fun s : ℂ => Λ + Λ * (s - a) + (s - a) ^ 2 * J s)
      (𝓝[≠] a) (𝓝 Λ) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlimit : Tendsto (fun s : ℂ => (s - a) ^ 2 * Phi U s) (𝓝[≠] a) (𝓝 Λ) := by
    apply hp.congr'
    filter_upwards [hPhi, self_mem_nhdsWithin] with s hs hsa
    have hn : s - a ≠ 0 := sub_ne_zero.mpr (by simpa using hsa)
    rw [hs]
    field_simp [hn]
    <;> ring
  exact ⟨haD, ha0, him, hm, hΛ, hMorder, horder,
    source_normalized_limit U hρ, hlimit, J, hJ, hPhi⟩


end
end D5.S3.Weil.Mertens.PsiLaplaceForcing
