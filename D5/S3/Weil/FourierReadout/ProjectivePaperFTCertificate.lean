/- GID: D5/S3/Weil/FourierReadout/ProjectivePaperFTCertificate
   generality: G
   mirror-B: D5/B/S3/Weil/FourierReadout/ProjectivePaperFTCertificate
   mirror-E: none(waiver:analytic-error-certificate)
   anchors: []
   digest: Consume Rayleigh projective capture in the existing paperFT integral with a sharp Fourier nonvanishing test. -/

import D5.S3.Weil.FourierReadout.WindowPaperFTReadout
import D5.S3.Observer.Hankel.ProjectiveReadoutSharpness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.FourierReadout.ProjectivePaperFTCertificate

open MeasureTheory Set
open D5.S3.Weil.FourierReadout.WindowPaperFTReadout
open D5.S3.Observer.Hankel.ProjectiveRayleighReadout
open D5.S3.Observer.Hankel.ProjectiveReadoutSharpness
open scoped ComplexInnerProductSpace

/-- The candidate-adapted error bound is now about the actual existing Fourier
integral. Its representer is constructed, not passed as an identification oracle. -/
theorem paperFT_projective_squared_error {a : ℝ} (k w : WindowL2 a) (delta : ℝ)
    (hk : ‖k‖ = 1) (ho : ⟪k, w⟫_ℂ = 0) (he : ‖w‖ ^ 2 ≤ delta) (z : ℂ) :
    ‖Zeta23.paperFT ((Icc (-a) a).indicator ((k + w) : ℝ → ℂ)) z -
      Zeta23.paperFT ((Icc (-a) a).indicator (k : ℝ → ℂ)) z‖ ^ 2 ≤
      (‖windowKernel a z‖ ^ 2 -
        ‖Zeta23.paperFT ((Icc (-a) a).indicator (k : ℝ → ℂ)) z‖ ^ 2) * delta := by
  simpa only [paperFT_window_eq_inner] using
    centered_readout_error_bound k (windowKernel a z) w delta hk ho he

/-- Sharp Fourier nonvanishing on the entire closed orthogonal L2 error ball.
The word sharp concerns this ball, not all errors realizable by a fixed Weil operator. -/
theorem paperFT_robust_nonvanishing_iff {a : ℝ} (k : WindowL2 a) (delta : ℝ)
    (hk : ‖k‖ = 1) (hd : 0 ≤ delta) (z : ℂ) :
    (∀ w : WindowL2 a, ⟪k, w⟫_ℂ = 0 → ‖w‖ ^ 2 ≤ delta →
      Zeta23.paperFT ((Icc (-a) a).indicator ((k + w) : ℝ → ℂ)) z ≠ 0) ↔
        delta * ‖windowKernel a z‖ ^ 2 <
          (1 + delta) * ‖Zeta23.paperFT ((Icc (-a) a).indicator (k : ℝ → ℂ)) z‖ ^ 2 := by
  simpa only [paperFT_window_eq_inner] using
    robust_readout_angle_iff k (windowKernel a z) delta hk hd

/-- At real frequencies the exact sharp threshold is a comparison with
2*a*delta. This uses ordinary Lebesgue normalization and needs no kernel quadrature. -/
theorem paperFT_real_robust_nonvanishing_iff {a : ℝ} (ha : 0 ≤ a)
    (k : WindowL2 a) (delta : ℝ) (hk : ‖k‖ = 1) (hd : 0 ≤ delta) (t : ℝ) :
    (∀ w : WindowL2 a, ⟪k, w⟫_ℂ = 0 → ‖w‖ ^ 2 ≤ delta →
      Zeta23.paperFT ((Icc (-a) a).indicator ((k + w) : ℝ → ℂ)) (t : ℂ) ≠ 0) ↔
        delta * (2 * a) < (1 + delta) *
          ‖Zeta23.paperFT ((Icc (-a) a).indicator (k : ℝ → ℂ)) (t : ℂ)‖ ^ 2 := by
  rw [paperFT_robust_nonvanishing_iff k delta hk hd, windowKernel_norm_sq_real ha]

/-- The projective error budget produces a bound uniform on a complete
horizontal strip. No Fourier differentiability or pointwise regularity of w is assumed. -/
theorem paperFT_projective_strip_bound {a b : ℝ} (ha : 0 ≤ a)
    (k w : WindowL2 a) (delta : ℝ) (he : ‖w‖ ^ 2 ≤ delta)
    (z : ℂ) (hz : |z.im| ≤ b) :
    ‖Zeta23.paperFT ((Icc (-a) a).indicator ((k + w) : ℝ → ℂ)) z -
      Zeta23.paperFT ((Icc (-a) a).indicator (k : ℝ → ℂ)) z‖ ≤
        (Real.sqrt (2 * a) * Real.exp (b * a)) * Real.sqrt delta := by
  have hd : 0 ≤ delta := (sq_nonneg _).trans he
  have hn : ‖w‖ ≤ Real.sqrt delta := by
    have hs := Real.sq_sqrt hd
    nlinarith [norm_nonneg w, Real.sqrt_nonneg delta]
  have h := paperFT_window_sub_le ha (k + w) k z hz
  simp only [add_sub_cancel_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left hn (by positivity))

/-- End-to-end actual Fourier consumer of the previously proved complex
Rayleigh enclosure. There is no supplied Fourier/L2 identity or error bound.
The genuine operator-domain inequalities and actual eigenvector remain inputs. -/
theorem rayleigh_paperFT_certificate {a b : ℝ} (ha : 0 ≤ a)
    {D : Type*} [AddCommGroup D] [Module ℂ D]
    (ι A : D →ₗ[ℂ] WindowL2 a) (k u : D) (lower upper threshold lam : ℝ)
    (hsym : ∀ x y : D, ⟪ι x, A y⟫_ℂ = ⟪A x, ι y⟫_ℂ)
    (hk : ‖ι k‖ = 1) (hu : ι u ≠ 0) (hAu : A u = (lam : ℂ) • ι u)
    (hlower : lower ≤ lam) (hlam : lam < threshold)
    (hupper : (⟪ι k, A k⟫_ℂ).re ≤ upper) (hthreshold : upper < threshold)
    (hcoercive : ∀ f : D, ⟪ι k, ι f⟫_ℂ = 0 →
      threshold * ‖ι f‖ ^ 2 ≤ (⟪ι f, A f⟫_ℂ).re) :
    let alpha := ⟪ι k, ι u⟫_ℂ
    let delta := (upper - lower) / (threshold - lower)
    alpha ≠ 0 ∧ 0 ≤ delta ∧
      ∀ z : ℂ,
        ‖Zeta23.paperFT ((Icc (-a) a).indicator ((alpha⁻¹ • ι u) : ℝ → ℂ)) z -
          Zeta23.paperFT ((Icc (-a) a).indicator (ι k : ℝ → ℂ)) z‖ ^ 2 ≤
          (‖windowKernel a z‖ ^ 2 -
            ‖Zeta23.paperFT ((Icc (-a) a).indicator (ι k : ℝ → ℂ)) z‖ ^ 2) * delta ∧
        (|z.im| ≤ b →
          ‖Zeta23.paperFT ((Icc (-a) a).indicator ((alpha⁻¹ • ι u) : ℝ → ℂ)) z -
            Zeta23.paperFT ((Icc (-a) a).indicator (ι k : ℝ → ℂ)) z‖ ≤
            (Real.sqrt (2 * a) * Real.exp (b * a)) * Real.sqrt delta) ∧
        (delta * ‖windowKernel a z‖ ^ 2 <
          (1 + delta) * ‖Zeta23.paperFT ((Icc (-a) a).indicator (ι k : ℝ → ℂ)) z‖ ^ 2 →
          Zeta23.paperFT ((Icc (-a) a).indicator (ι u : ℝ → ℂ)) z ≠ 0) := by
  obtain ⟨halpha, ho, he, hd, _⟩ := rayleigh_projective_enclosure ι A k u
    lower upper threshold lam hsym hk hu hAu hlower hlam hupper hthreshold hcoercive
  let alpha := ⟪ι k, ι u⟫_ℂ
  let delta := (upper - lower) / (threshold - lower)
  let w := ι (alpha⁻¹ • u - k)
  have hsum : ι k + w = alpha⁻¹ • ι u := by
    dsimp only [w]
    rw [map_sub, map_smul]
    abel
  refine ⟨halpha, hd, ?_⟩
  intro z
  have hs := paperFT_projective_squared_error (ι k) w delta hk ho he z
  rw [hsum] at hs
  refine ⟨hs, ?_, ?_⟩
  · intro hz
    have h := paperFT_projective_strip_bound ha (ι k) w delta he z hz
    rwa [hsum] at h
  · intro hmargin
    have hn := (paperFT_robust_nonvanishing_iff (ι k) delta hk hd z).mpr hmargin w ho he
    rw [hsum, paperFT_window_eq_inner, inner_smul_right] at hn
    rw [paperFT_window_eq_inner]
    intro hz
    exact hn (by rw [hz, mul_zero])

#print axioms rayleigh_paperFT_certificate
#print axioms paperFT_robust_nonvanishing_iff

end D5.S3.Weil.FourierReadout.ProjectivePaperFTCertificate
