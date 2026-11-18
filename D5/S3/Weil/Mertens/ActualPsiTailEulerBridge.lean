/- GID: D5/S3/Weil/Mertens/ActualPsiTailEulerBridge
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/ActualPsiTailEulerBridge
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   utility: none
   digest: Actual psi-tail continuation and Euler forcing. -/

import D5.S3.Analytic.Laplace.ActivationTailEuler
import D5.S3.Analytic.Laplace.EulerPoleObstruction
import D5.S3.Weil.ZeroSum
import D5.S3.Weil.Mertens.ThetaLaplaceContinuation
import D5.S3.Weil.Mertens.WeightedPrimeLimit
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope

/-! The actual source calculus consumed by the signed psi-tail Euler equation. -/

namespace D5.S3.Weil.Mertens.PsiLaplaceContinuation

open Real Set MeasureTheory Filter Asymptotics Complex
open scoped BigOperators Topology
open D5.S3.Analytic.Laplace.EulerPoleObstruction

noncomputable section

def qpsi (u : ℝ) : ℝ :=
  Real.exp (-u) * (Chebyshev.psi (Real.exp u) - Real.exp u)

def Qpsi (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi U, Complex.exp (-s * (u : ℂ)) * (qpsi u : ℂ)

def Apsi (U : ℝ) (s : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..U, Complex.exp (-s * (u : ℂ)) * (qpsi u : ℂ)

def Mpsi (U : ℝ) (s : ℂ) : ℂ :=
  -(1 + logDeriv riemannZeta₁ (1 + s)) / (1 + s) - Apsi U s

theorem qpsi_measurable : Measurable qpsi := by
  unfold qpsi
  exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-u))).mul
    ((Chebyshev.psi_mono.measurable.comp (by fun_prop)).sub (by fun_prop))

private lemma qpsi_bound (u : ℝ) : ‖qpsi u‖ ≤ Real.log 4 + 4 + 1 := by
  have he := (Real.exp_pos u).le
  have hp := Chebyshev.psi_nonneg (Real.exp u)
  have hb := Chebyshev.psi_le_const_mul_self he
  rw [qpsi, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  calc
    Real.exp (-u) * |Chebyshev.psi (Real.exp u) - Real.exp u|
        ≤ Real.exp (-u) * (Chebyshev.psi (Real.exp u) + Real.exp u) := by
      gcongr
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hp, abs_of_nonneg he])
    _ ≤ Real.exp (-u) * ((Real.log 4 + 4) * Real.exp u + Real.exp u) := by gcongr
    _ = Real.log 4 + 4 + 1 := by
      rw [← add_one_mul, mul_left_comm, ← Real.exp_add]
      simp

/-- Original psi error integrability, transported by t = exp u. -/
theorem qpsi_integrable : IntegrableOn qpsi (Ioi (Real.log 2)) := by
  have ht := WeightedPrimeLimit.chebyshev_error_kernel_integrable.mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2))
  have he := (integrableOn_comp_exp_Ioi
    (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Real.log 2)).mpr
    (by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using ht)
  refine he.congr_fun ?_ measurableSet_Ioi
  intro u _
  dsimp [qpsi]
  rw [Real.exp_neg]
  field_simp

private theorem source_integrable (U : ℝ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ)) * (qpsi u : ℂ))
      (Ioi U) := by
  exact (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) U).mul_bdd
    qpsi_measurable.complex_ofReal.aestronglyMeasurable.restrict
    (Eventually.of_forall fun u => by simpa using qpsi_bound u)

private lemma Qpsi_cutoff (U : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Qpsi U s = Qpsi 0 s - Apsi U s := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi'
    (source_integrable 0 hs) (source_integrable U hs)
  change Qpsi 0 s - Qpsi U s = Apsi U s at h
  linear_combination -h

/-- The actual von Mangoldt Mellin identity in its absolute-convergence region. -/
private theorem psi_mellin {z : ℂ} (hz : 1 < z.re) :
    -logDeriv riemannZeta z = z * ∫ x in Ioi (1 : ℝ),
      (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(z + 1)) := by
  have h := LSeries_eq_mul_integral_of_nonneg
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (by norm_num : (0 : ℝ) ≤ 1) hz CompleteChebyshevTailIdentity.mangoldt_prefix_bigO
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  have he : LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) z =
      -logDeriv riemannZeta z := by
    simpa only [logDeriv_apply, neg_div, ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz
  rw [he] at h
  have hprefix (x : ℝ) :
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k) = Chebyshev.psi x := rfl
  simpa only [← Complex.ofReal_sum, hprefix] using h

private lemma kernel_eq (s : ℂ) (u : ℝ) :
    kernel qpsi s u = Complex.exp (-(s + 1) * (u : ℂ)) *
      ((Chebyshev.psi (Real.exp u) - Real.exp u : ℝ) : ℂ) := by
  unfold kernel qpsi
  rw [Complex.ofReal_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma psi_exp_point (s : ℂ) (u : ℝ) :
    Real.exp u • ((Chebyshev.psi (Real.exp u) : ℂ) *
      (Real.exp u : ℂ) ^ (-((1 + s) + 1))) =
      kernel qpsi s u + Complex.exp (-s * (u : ℂ)) := by
  rw [ThetaLaplaceContinuation.cpow_exp, kernel_eq, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_exp]
  have he : Complex.exp (-(s + 1) * (u : ℂ)) * Complex.exp (u : ℂ) =
      Complex.exp (-s * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hprod : Complex.exp (u : ℂ) *
      Complex.exp ((u : ℂ) * (-((1 + s) + 1))) =
      Complex.exp (-(s + 1) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [mul_left_comm, hprod]
  linear_combination he

private lemma Qpsi_zero_raw {s : ℂ} (hs : 0 < s.re) :
    Qpsi 0 s = -logDeriv riemannZeta (1 + s) / (1 + s) - 1 / s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hz0 : 1 + s ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  have hm := psi_mellin (z := 1 + s) (by simp; linarith)
  have he := integral_comp_exp_Ioi
    (fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-((1 + s) + 1))) 0
  simp only [Real.exp_zero] at he
  have hpt : (fun u : ℝ => Real.exp u • ((Chebyshev.psi (Real.exp u) : ℂ) *
      (Real.exp u : ℂ) ^ (-((1 + s) + 1)))) =
      (fun u => kernel qpsi s u + Complex.exp (-s * (u : ℂ))) :=
    funext (psi_exp_point s)
  rw [hpt] at he
  have hi : IntegrableOn (kernel qpsi s) (Ioi 0) := source_integrable 0 hs
  rw [integral_add hi
    (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0)] at he
  have hem : (∫ u in Ioi (0 : ℝ), Complex.exp (-s * (u : ℂ))) = 1 / s := by
    simpa using integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  rw [hem] at he
  change Qpsi 0 s + 1 / s = _ at he
  rw [← he] at hm
  have hd : -logDeriv riemannZeta (1 + s) / (1 + s) = Qpsi 0 s + 1 / s := by
    rw [hm]
    field_simp
  linear_combination -hd

private lemma normalized_zeta_ne_zero_right {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₁ (1 + s) ≠ 0 := by
  have hz1 : 1 + s ≠ 1 := by simpa using Complex.ne_zero_of_re_pos hs
  intro hn
  have he := riemannZeta_eq_inv_sub_mul hz1
  rw [hn, mul_zero] at he
  exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith) he

/-- The finite cutoff is subtracted. No prime-power correction occurs. -/
theorem Qpsi_eq_Mpsi (U : ℝ) {s : ℂ} (hs : 0 < s.re) : Qpsi U s = Mpsi U s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hz0 : 1 + s ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  have hz1 : 1 + s ≠ 1 := by simpa using hs0
  rw [Qpsi_cutoff U hs, Qpsi_zero_raw hs,
    ThetaLaplaceContinuation.normalized_logDeriv hz1 (normalized_zeta_ne_zero_right hs)]
  unfold Mpsi
  field_simp [hs0, hz0]
  ring

end
end D5.S3.Weil.Mertens.PsiLaplaceContinuation

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

end
end D5.S3.Weil.Mertens.PsiLaplaceForcing

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

end D5.S3.Weil.Mertens.PsiLaplaceForcing
