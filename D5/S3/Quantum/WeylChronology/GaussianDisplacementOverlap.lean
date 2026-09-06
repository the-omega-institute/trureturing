/- GID: D5/S3/Quantum/WeylChronology/GaussianDisplacementOverlap
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:exact-continuous-integral)
   anchors: []
   digest: The normalized overlap of an actual Gaussian wavefunction and its Weyl displacement is evaluated exactly. -/

import D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian reference overlap for the concrete Weyl action

The real seed exp(-s*q^2), s>0, is square integrable and has strictly positive
squared norm. Its normalized overlap is defined by an actual Bochner integral,
not by the desired exponential formula. The integral is evaluated using the
pinned Mathlib `integral_cexp_quadratic`; the Gaussian Fourier theorem is not
reproved. No abstract CCR, coherent-state overlap axiom, or Fock cutoff is used.

For beta=x+iy and squeezing axis fixed at zero, the answer is
exp(-(s*x^2+y^2/s)/2). This is the centered specialization of Fluehmann and
Home, PRL 125, 043602 (2020), arXiv:1907.06478, equation (5), with s=exp(2r).
Their equation (3) supplies the phase-sensitive readout. Convention: the
existing displacement acts as exp(i*(2yq-xy))*f(q-x), so [Q,P]=i/2.

Library-first audit at #5750 head 26e28252510866ce6bb8f6098b1a2916f7b1b519:
`GaussianSelfDualPi` owns a different Fourier-self-duality characterization.
`RamseyResidualOverlap` accepts a supplied complex overlap; no actual Gaussian
Weyl overlap owner or matching open draft was found. Mathlib is pinned to
 db584cd6d46c92f209a44c0f1c829460d327499d.

The named consumer is GoldenGaussianClosure. The new physical edge evaluates
that consumer's previously supplied overlap. Full L2 representation theory,
operator domains and arbitrary mixed or non-Gaussian states are outside scope.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GaussianDisplacementOverlap

open MeasureTheory
open D5.S3.Quantum.WeylChronology.SchrodingerDisplacement

noncomputable section

/-- A real, not yet normalized, Gaussian wavefunction. -/
def gaussianSeed (s q : ℝ) : ℂ := (Real.exp (-s * q ^ 2) : ℂ)

/-- The actual squared-norm integral of the Gaussian seed. -/
def gaussianMass (s : ℝ) : ℂ :=
  ∫ q : ℝ, star (gaussianSeed s q) * gaussianSeed s q

/-- Normalized displacement expectation. The denominator is the same seed's
actual squared-norm integral, whose nonvanishing is proved below. -/
def gaussianOverlap (s x y : ℝ) : ℂ :=
  (∫ q : ℝ, star (gaussianSeed s q) * displacement x y (gaussianSeed s) q) /
    gaussianMass s

/-- The anisotropic displacement cost, in the existing quadrature convention. -/
def displacementCost (s x y : ℝ) : ℝ := (s * x ^ 2 + y ^ 2 / s) / 2

private theorem seed_star (s q : ℝ) : star (gaussianSeed s q) = gaussianSeed s q := by
  simp [gaussianSeed]

private theorem seed_self_integrand (s q : ℝ) :
    star (gaussianSeed s q) * gaussianSeed s q =
      (Real.exp (-(2 * s) * q ^ 2) : ℂ) := by
  rw [seed_star]
  change (Real.exp (-s * q ^ 2) : ℂ) * (Real.exp (-s * q ^ 2) : ℂ) = _
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

private theorem seed_intensity (s q : ℝ) :
    Complex.normSq (gaussianSeed s q) = Real.exp (-(2 * s) * q ^ 2) := by
  have h := congrArg Complex.re (seed_self_integrand s q)
  simpa [gaussianSeed, Complex.normSq_apply] using h

/-- Square integrability is proved before interpreting the normalized overlap. -/
theorem gaussian_intensity_integrable (s : ℝ) (hs : 0 < s) :
    Integrable (fun q : ℝ => Complex.normSq (gaussianSeed s q)) := by
  simp_rw [seed_intensity]
  exact integrable_exp_neg_mul_sq (mul_pos (by norm_num) hs)

/-- The normalization integral is real and strictly positive for s>0. -/
theorem gaussian_mass_value (s : ℝ) :
    gaussianMass s = (Real.sqrt (Real.pi / (2 * s)) : ℂ) := by
  unfold gaussianMass
  simp_rw [seed_self_integrand]
  rw [integral_complex_ofReal, integral_gaussian]

/-- The physical Gaussian normalization never divides by zero. -/
theorem gaussian_mass_ne_zero (s : ℝ) (hs : 0 < s) : gaussianMass s ≠ 0 := by
  rw [gaussian_mass_value]
  exact Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (div_pos Real.pi_pos (mul_pos (by norm_num) hs))).ne'

private theorem overlap_integrand (s x y q : ℝ) :
    star (gaussianSeed s q) * displacement x y (gaussianSeed s) q =
      Complex.exp (-(2 * (s : ℂ)) * (q : ℂ) ^ 2 +
        (2 * (s : ℂ) * (x : ℂ) + 2 * (y : ℂ) * Complex.I) * (q : ℂ) +
        (-(s : ℂ) * (x : ℂ) ^ 2 - (x : ℂ) * (y : ℂ) * Complex.I)) := by
  rw [seed_star]
  unfold displacement gaussianSeed
  simp only [Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The displaced overlap integrand is genuinely integrable. -/
theorem gaussian_overlap_integrable (s x y : ℝ) (hs : 0 < s) :
    Integrable (fun q : ℝ =>
      star (gaussianSeed s q) * displacement x y (gaussianSeed s) q) := by
  simp_rw [overlap_integrand]
  exact integrable_cexp_quadratic'
    (by simpa using (show -(2 * s) < 0 by linarith [hs])) _ _

private theorem raw_overlap_value (s x y : ℝ) (hs : 0 < s) :
    (∫ q : ℝ, star (gaussianSeed s q) * displacement x y (gaussianSeed s) q) =
      ((Real.pi : ℂ) / (2 * (s : ℂ))) ^ (1 / 2 : ℂ) *
        (Real.exp (-displacementCost s x y) : ℂ) := by
  simp_rw [overlap_integrand]
  rw [integral_cexp_quadratic
    (by simpa using (show -(2 * s) < 0 by linarith [hs]))]
  simp only [neg_neg]
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hexponent :
      (-(s : ℂ) * (x : ℂ) ^ 2 - (x : ℂ) * (y : ℂ) * Complex.I) -
        (2 * (s : ℂ) * (x : ℂ) + 2 * (y : ℂ) * Complex.I) ^ 2 /
          (4 * -(2 * (s : ℂ))) = (-displacementCost s x y : ℝ) := by
    unfold displacementCost
    push_cast
    field_simp [hsC] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [hexponent, ← Complex.ofReal_exp]

/-- The exact normalized two-quadrature overlap of the concrete Gaussian seed. -/
theorem gaussian_overlap_exact (s x y : ℝ) (hs : 0 < s) :
    gaussianOverlap s x y = (Real.exp (-displacementCost s x y) : ℂ) := by
  have hmass : gaussianMass s =
      ((Real.pi : ℂ) / (2 * (s : ℂ))) ^ (1 / 2 : ℂ) := by
    simpa [gaussianMass, displacement, displacementCost] using raw_overlap_value s 0 0 hs
  unfold gaussianOverlap
  rw [raw_overlap_value s x y hs, ← hmass]
  field_simp [gaussian_mass_ne_zero s hs] <;> ring

/-- The overlap's attenuation cost is nonnegative. -/
theorem displacement_cost_nonneg (s x y : ℝ) (hs : 0 < s) :
    0 ≤ displacementCost s x y := by
  unfold displacementCost
  positivity

/-- Physical contractivity follows from the evaluated integral, not an input premise. -/
theorem gaussian_overlap_norm_le_one (s x y : ℝ) (hs : 0 < s) :
    ‖gaussianOverlap s x y‖ ≤ 1 := by
  rw [gaussian_overlap_exact s x y hs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (displacement_cost_nonneg s x y hs))

/-- Centered Gaussians lose overlap only at quadratic order in residual displacement. -/
theorem gaussian_overlap_defect_le_cost (s x y : ℝ) (hs : 0 < s) :
    ‖gaussianOverlap s x y - 1‖ ≤ displacementCost s x y := by
  have he : Real.exp (-displacementCost s x y) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (displacement_cost_nonneg s x y hs))
  rw [gaussian_overlap_exact s x y hs, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr he)]
  linarith [Real.one_sub_le_exp_neg (displacementCost s x y)]

#print axioms gaussian_intensity_integrable
#print axioms gaussian_mass_ne_zero
#print axioms gaussian_overlap_integrable
#print axioms gaussian_overlap_exact
#print axioms gaussian_overlap_norm_le_one
#print axioms gaussian_overlap_defect_le_cost

end
end D5.S3.Quantum.WeylChronology.GaussianDisplacementOverlap
