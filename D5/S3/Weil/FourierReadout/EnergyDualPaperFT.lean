/- GID: D5/S3/Weil/FourierReadout/EnergyDualPaperFT
   generality: G
   mirror-B: D5/B/S3/Weil/FourierReadout/EnergyDualPaperFT
   mirror-E: none(waiver:residual-certified-Fourier-limit)
   anchors: []
   digest: Bound the existing Fourier integral and transfer its limit using actual energy-dual trial residuals. -/

import D5.S3.Weil.FourierReadout.WindowPaperFTReadout
import D5.S3.Weil.ZetaLinear.ProjectiveEnergyDual
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
This module uses the previously identified actual paperFT representer.
A trial for each readout replaces the isotropic kernel norm by a full-residual
energy-dual certificate. An upper bound on the resulting scalar expression
can be certified separately with interval arithmetic and all-mode tails.
No finite retained residual may be silently substituted for the full one.
The operator-domain, eigenvector and full coercivity hypotheses remain.
The all-scale rate and the correctly normalized candidate limit are explicit
remaining inputs. Nothing here proves the arithmetic Weil instance or RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.FourierReadout.EnergyDualPaperFT

open Filter MeasureTheory Set
open D5.S3.Weil.FourierReadout.WindowPaperFTReadout
open D5.S3.Weil.ZetaLinear.CoerciveDualCertificate
open D5.S3.Weil.ZetaLinear.ProjectiveEnergyDual
open scoped ComplexInnerProductSpace Topology

/-- Full-domain Rayleigh data and any orthogonal dual trial bound the actual
existing Fourier integral. The scalar sensitivity is computed from the
trial, its energy and the full shifted-action residual. -/
theorem rayleigh_paperFT_dual_error {a : ℝ}
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] WindowL2 a) (k u : D) (ell U T lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0) (hAu : A u = (lam : ℂ) • ι u)
    (hell : ell ≤ lam) (hlam : lam < T)
    (hU : (⟪ι k, A k⟫_ℂ).re ≤ U) (hT : U < T)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      T * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (z : ℂ) (v : D) (hv : ⟪ι k, ι v⟫_ℂ = 0) :
    let alpha := ⟪ι k, ι u⟫_ℂ
    let C := dualBudget ι (shiftedAction ι A ell) k (windowKernel a z) (T - ell) v
    alpha ≠ 0 ∧ 0 ≤ C ∧
      ‖Zeta23.paperFT ((Icc (-a) a).indicator ((alpha⁻¹ • ι u) : ℝ → ℂ)) z -
        Zeta23.paperFT ((Icc (-a) a).indicator (ι k : ℝ → ℂ)) z‖ ^ 2 ≤ C * (U - ell) := by
  simpa only [paperFT_window_eq_inner] using
    rayleigh_dual_readout ι A k u ell U T lam hsym hk hu hAu hell hlam hU hT
      hcoercive (windowKernel a z) v hv

/-- A strict full-residual energy margin certifies a nonzero Fourier readout
of the actual eigenvector, without asserting norm-ball necessity. -/
theorem rayleigh_paperFT_dual_nonzero {a : ℝ}
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] WindowL2 a) (k u : D) (ell U T lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0) (hAu : A u = (lam : ℂ) • ι u)
    (hell : ell ≤ lam) (hlam : lam < T)
    (hU : (⟪ι k, A k⟫_ℂ).re ≤ U) (hT : U < T)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      T * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re)
    (z : ℂ) (v : D) (hv : ⟪ι k, ι v⟫_ℂ = 0)
    (hmargin : dualBudget ι (shiftedAction ι A ell) k (windowKernel a z) (T - ell) v *
      (U - ell) < ‖Zeta23.paperFT ((Icc (-a) a).indicator (ι k : ℝ → ℂ)) z‖ ^ 2) :
    Zeta23.paperFT ((Icc (-a) a).indicator (ι u : ℝ → ℂ)) z ≠ 0 := by
  obtain ⟨_, _, hb⟩ := rayleigh_paperFT_dual_error ι A k u ell U T lam
    hsym hk hu hAu hell hlam hU hT hcoercive z v hv
  intro hz
  have hzero : Zeta23.paperFT ((Icc (-a) a).indicator
      (((⟪ι k, ι u⟫_ℂ)⁻¹ • ι u) : ℝ → ℂ)) z = 0 := by
    rw [paperFT_window_eq_inner] at hz ⊢
    rw [inner_smul_right, hz, mul_zero]
  rw [hzero, zero_sub, norm_neg] at hb
  exact (not_le_of_gt hmargin) hb

/-- A scalar upper envelope for the actual residual-based dual coefficients
transfers the candidate Fourier limit to the same normalized eigenmodes.
Only the energy-direction rate ||c_j||^2 * B_j * (U_j-ell_j) -> 0 is required;
no global strip-kernel norm factor is imposed. K may be any target set.
Candidate convergence and full-domain arithmetic conditions remain explicit. -/
theorem rayleigh_paperFT_dual_uniform_limit
    {J : Type*} (l : Filter J) (a : J → ℝ)
    (D : J → Type*) [∀ j, AddCommGroup (D j)] [∀ j, Module ℂ (D j)]
    (ι A : ∀ j, D j →ₗ[ℂ] WindowL2 (a j)) (k u : ∀ j, D j)
    (ell U T lam : J → ℝ) (c : J → ℂ) (F : ℂ → ℂ) (K : Set ℂ)
    (v : ∀ j, ℂ → D j) (B : J → ℝ)
    (hsym : ∀ j (x y : D j), ⟪ι j x, A j y⟫_ℂ = ⟪A j x, ι j y⟫_ℂ)
    (hk : ∀ j, ‖ι j (k j)‖ = 1) (hu : ∀ j, ι j (u j) ≠ 0)
    (hAu : ∀ j, A j (u j) = (lam j : ℂ) • ι j (u j))
    (hell : ∀ j, ell j ≤ lam j) (hlam : ∀ j, lam j < T j)
    (hU : ∀ j, (⟪ι j (k j), A j (k j)⟫_ℂ).re ≤ U j) (hT : ∀ j, U j < T j)
    (hcoercive : ∀ j (f : D j), ⟪ι j (k j), ι j f⟫_ℂ = 0 →
      T j * ‖ι j f‖ ^ 2 ≤ (⟪ι j f, A j f⟫_ℂ).re)
    (hv : ∀ j z, z ∈ K → ⟪ι j (k j), ι j (v j z)⟫_ℂ = 0)
    (hB : ∀ j z, z ∈ K →
      dualBudget (ι j) (shiftedAction (ι j) (A j) (ell j)) (k j)
        (windowKernel (a j) z) (T j - ell j) (v j z) ≤ B j)
    (hsmall : Tendsto (fun j => ‖c j‖ ^ 2 * (B j * (U j - ell j))) l (𝓝 0))
    (hcandidate : TendstoUniformlyOn (fun j z => c j *
      Zeta23.paperFT ((Icc (-a j) (a j)).indicator (ι j (k j) : ℝ → ℂ)) z) F l K) :
    TendstoUniformlyOn (fun j z => c j * Zeta23.paperFT
      ((Icc (-a j) (a j)).indicator
        (((⟪ι j (k j), ι j (u j)⟫_ℂ)⁻¹ • ι j (u j)) : ℝ → ℂ)) z) F l K := by
  have hE (j : J) : 0 ≤ U j - ell j := by
    obtain ⟨_, _, h0, h1⟩ := rayleigh_shifted_energy_bound (ι j) (A j) (k j) (u j)
      (ell j) (U j) (T j) (lam j) (hsym j) (hk j) (hu j) (hAu j) (hell j)
      (hlam j) (hU j) (hT j) (hcoercive j)
    exact h0.trans h1
  let actual : J → ℂ → ℂ := fun j z => Zeta23.paperFT
    ((Icc (-a j) (a j)).indicator
      (((⟪ι j (k j), ι j (u j)⟫_ℂ)⁻¹ • ι j (u j)) : ℝ → ℂ)) z
  let candidate : J → ℂ → ℂ := fun j z =>
    Zeta23.paperFT ((Icc (-a j) (a j)).indicator (ι j (k j) : ℝ → ℂ)) z
  have herr : TendstoUniformlyOn (fun j z => c j * (actual j z - candidate j z))
      (fun _ => 0) l K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    filter_upwards [(tendsto_order.mp hsmall).2 (eps ^ 2) (sq_pos_of_pos heps)]
      with j hj z hz
    obtain ⟨_, _, hb⟩ := rayleigh_paperFT_dual_error (ι j) (A j) (k j) (u j)
      (ell j) (U j) (T j) (lam j) (hsym j) (hk j) (hu j) (hAu j) (hell j)
      (hlam j) (hU j) (hT j) (hcoercive j) z (v j z) (hv j z hz)
    have hupper := hb.trans (mul_le_mul_of_nonneg_right (hB j z hz) (hE j))
    have hscaled := mul_le_mul_of_nonneg_left hupper (sq_nonneg ‖c j‖)
    have hsquare : ‖c j * (actual j z - candidate j z)‖ ^ 2 ≤
        ‖c j‖ ^ 2 * (B j * (U j - ell j)) := by
      rw [norm_mul, mul_pow]
      exact hscaled
    rw [dist_zero_left]
    nlinarith [norm_nonneg (c j * (actual j z - candidate j z))]
  have h := herr.add hcandidate
  simpa only [actual, candidate, Pi.add_apply, mul_sub, sub_add_cancel, zero_add] using h

#print axioms rayleigh_paperFT_dual_error
#print axioms rayleigh_paperFT_dual_uniform_limit

end D5.S3.Weil.FourierReadout.EnergyDualPaperFT
