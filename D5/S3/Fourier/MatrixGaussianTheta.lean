/- GID: D5/S3/Fourier/MatrixGaussianTheta
   generality: G
   mirror-B: D5/B/S3/Fourier/MatrixGaussianTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Principal-branch theta inversion for real positive definite matrices. -/

import D5.S3.Fourier.MatrixGaussianPoisson

/-! # Theta inversion in fixed real coordinates -/

set_option autoImplicit false

open scoped BigOperators
open Matrix

namespace D5.S3.Fourier.MatrixGaussian
noncomputable section

/-- The theta series of a real coordinate Gram matrix. -/
def theta {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (τ : ℂ) : ℂ :=
  ∑' a : Fin r → ℤ, Complex.exp
    (Real.pi * Complex.I * τ * (quadratic A (fun i => (a i : ℝ)) : ℂ))

/-- Upper half-plane convergence of the actual integer-coordinate theta series. -/
theorem summable_norm_theta {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.PosDef) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun a : Fin r → ℤ => ‖Complex.exp
      (Real.pi * Complex.I * τ * (quadratic A (fun i => (a i : ℝ)) : ℂ))‖) := by
  convert summable_norm_gaussian A hA (-Complex.I * τ) (by simpa using hτ) using 1
  funext a
  congr 2
  ring

/-- Inversion exchanges a positive matrix theta series with the inverse-form
series. The power is on the principal branch and dimension zero is included. -/
theorem theta_inversion {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosDef)
    (τ : ℂ) (hτ : 0 < τ.im) :
    theta A (-1 / τ) = (-Complex.I * τ) ^ ((r : ℂ) / 2) /
      (Real.sqrt A.det : ℂ) * theta A⁻¹ τ := by
  let z := -Complex.I * τ
  have hz : 0 < z.re := by simpa [z] using hτ
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hτ0 : τ ≠ 0 := by intro h; simpa [h] using hτ
  have hzi : 0 < (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have harg : z.arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have h := (poisson_gaussian A hA z⁻¹ hzi).2.2
  have hleft : -(Real.pi : ℂ) * z⁻¹ = Real.pi * Complex.I * (-1 / τ) := by
    dsimp [z]
    field_simp
    simp [Complex.I_sq]
    <;> ring
  have hright : -(Real.pi : ℂ) / z⁻¹ = Real.pi * Complex.I * τ := by
    dsimp [z]
    rw [div_inv_eq_mul]
    ring
  rw [hleft, hright, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg] at h
  have he : -(-(r : ℂ) / 2) = (r : ℂ) / 2 := by ring
  rw [he] at h
  simpa only [theta, div_eq_mul_inv, mul_comm (Real.sqrt A.det : ℂ)⁻¹] using h

#print axioms theta_inversion

end
end D5.S3.Fourier.MatrixGaussian
