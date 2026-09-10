/- GID: D5/S3/Weil/ZetaBridge/WeilMellinScaleFlow
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilMellinScaleFlow
   mirror-E: none(waiver:uniform-prolate-spectrum-and-scale-derivative-paper-bridges)
   anchors: []
   utility: none
   digest: Reuse the actual polynomial Mellin window to eliminate its moving upper endpoint and prove an exact centered Fourier scale difference. -/

import D5.S3.Weil.ZetaBridge.WeilPolynomialMellinWindow

/-!
# Exact scale dependence of the actual polynomial Mellin window

A fixed polynomial H(t)=sum B_r*t^(2r) on [-1,1] defines the physical
seed h_a(t)=H(exp(-a)*t). The existing polynomialMellinWindow therefore
has coefficients B_r*exp(-2r*a). Its Fourier integral is the existing
Zeta23.paperFT. No second Fourier transform or supplied scale error is used.

Multiplication by exp(-(1/2+i*z)*a) cancels the moving upper endpoint.
The resulting exact two-scale identity is the finite polynomial input to
the paper scale-flow equation and the executed uniform true-prolate model
transport. Spectral realization, changing visible integer sets, and the
uniform norm estimates are separately justified in the existing RH volume.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilMellinScaleFlow

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilPolynomialMellinWindow

/-- The original arithmetic window for the independently fixed rescaled seed.
The change in coefficients is the actual h_a(t)=H(exp(-a)*t) scaling. -/
def scaledPolynomialWindow (a : ℝ) (M d : ℕ) (B : ℕ → ℂ) : ℝ → ℂ :=
  polynomialMellinWindow a M d
    (fun r => B r * Complex.exp (-((2 * r : ℕ) : ℂ) * (a : ℂ)))

private theorem rate_split (r : ℕ) (z : ℂ) :
    mellinRate r z = ((2 * r : ℕ) : ℂ) + mellinRate 0 z := by
  simp only [mellinRate, mul_zero, Nat.cast_zero, zero_add]
  ring

private theorem centered_exponent_products (a l : ℝ) (r : ℕ) (z : ℂ) :
    Complex.exp (-mellinRate 0 z * (a : ℂ)) *
      Complex.exp (-((2 * r : ℕ) : ℂ) * (a : ℂ)) *
      Complex.exp (mellinRate r z * ((a - l : ℝ) : ℂ)) =
        Complex.exp (-mellinRate r z * (l : ℂ)) ∧
    Complex.exp (-mellinRate 0 z * (a : ℂ)) *
      Complex.exp (-((2 * r : ℕ) : ℂ) * (a : ℂ)) *
      Complex.exp (mellinRate r z * ((-a : ℝ) : ℂ)) =
        Complex.exp (-2 * mellinRate r z * (a : ℂ)) := by
  have hrate := rate_split r z
  constructor <;> rw [← Complex.exp_add, ← Complex.exp_add] <;>
    congr 1 <;> simp only [hrate, Complex.ofReal_sub, Complex.ofReal_neg] <;> ring

/-- Actual centered Fourier evaluation. The upper-endpoint term is independent
of a after the specified normalization; the remaining lower endpoint is exact.
Integrability of this window is supplied by the existing polynomial owner,
not assumed as a hypothesis. The original strip condition excludes poles. -/
theorem scaled_polynomial_centered_paperFT
    (a : ℝ) (M d : ℕ) (B : ℕ → ℂ) (z : ℂ)
    (hcut : ∀ m ∈ Finset.Icc 1 M, Real.log (m : ℝ) ≤ 2 * a)
    (hz : z.im < 1 / 2) :
    Complex.exp (-mellinRate 0 z * (a : ℂ)) *
      Zeta23.paperFT (scaledPolynomialWindow a M d B) z =
      4 * ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.range d,
        B r * (m : ℂ) ^ (2 * r) *
          ((Complex.exp (-mellinRate r z * (Real.log (m : ℝ) : ℂ)) -
            Complex.exp (-2 * mellinRate r z * (a : ℂ))) / mellinRate r z) := by
  unfold scaledPolynomialWindow
  rw [polynomial_mellin_window_paperFT a M d _ z hcut hz]
  rw [mul_left_comm (Complex.exp (-mellinRate 0 z * (a : ℂ))) 4]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨hupper, hlower⟩ := centered_exponent_products a (Real.log (m : ℝ)) r z
  calc
    _ = B r * (m : ℂ) ^ (2 * r) *
        ((Complex.exp (-mellinRate 0 z * (a : ℂ)) *
            Complex.exp (-((2 * r : ℕ) : ℂ) * (a : ℂ)) *
            Complex.exp (mellinRate r z * ((a - Real.log (m : ℝ) : ℝ) : ℂ)) -
          Complex.exp (-mellinRate 0 z * (a : ℂ)) *
            Complex.exp (-((2 * r : ℕ) : ℂ) * (a : ℂ)) *
            Complex.exp (mellinRate r z * ((-a : ℝ) : ℂ))) / mellinRate r z) := by ring
    _ = _ := by rw [hupper, hlower]

/-- The complete two-scale change of the same centered Fourier function in
one visible-integer chamber. No scalar candidate or Fourier discrepancy is
an input. At an activation endpoint the new integral has length zero; the
paper proof joins chambers there before deriving its uniform flow bound. -/
theorem scaled_polynomial_paperFT_scale_difference
    (a b : ℝ) (M d : ℕ) (B : ℕ → ℂ) (z : ℂ)
    (ha : ∀ m ∈ Finset.Icc 1 M, Real.log (m : ℝ) ≤ 2 * a)
    (hb : ∀ m ∈ Finset.Icc 1 M, Real.log (m : ℝ) ≤ 2 * b)
    (hz : z.im < 1 / 2) :
    Complex.exp (-mellinRate 0 z * (b : ℂ)) *
        Zeta23.paperFT (scaledPolynomialWindow b M d B) z -
      Complex.exp (-mellinRate 0 z * (a : ℂ)) *
        Zeta23.paperFT (scaledPolynomialWindow a M d B) z =
      4 * ∑ m ∈ Finset.Icc 1 M, ∑ r ∈ Finset.range d,
        B r * (m : ℂ) ^ (2 * r) *
          ((Complex.exp (-2 * mellinRate r z * (a : ℂ)) -
            Complex.exp (-2 * mellinRate r z * (b : ℂ))) / mellinRate r z) := by
  rw [scaled_polynomial_centered_paperFT b M d B z hb hz,
    scaled_polynomial_centered_paperFT a M d B z ha hz,
    ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  ring

#print axioms scaled_polynomial_centered_paperFT
#print axioms scaled_polynomial_paperFT_scale_difference

end D5.S3.Weil.ZetaBridge.WeilMellinScaleFlow
