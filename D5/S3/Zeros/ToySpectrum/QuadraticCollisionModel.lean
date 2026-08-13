/- GID: D5/S3/Zeros/ToySpectrum/QuadraticCollisionModel
   generality: I
   mirror-B: D5/B/S3/Zeros/ToySpectrum/QuadraticCollisionModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The z^2+t model exhibits root collision while preserving two roots with multiplicity. -/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

namespace D5.S3.Zeros.ToySpectrum.QuadraticCollisionModel

open Polynomial
open scoped ComplexConjugate

noncomputable def quadraticCollisionPolynomial (t : ℝ) : ℂ[X] :=
  X ^ 2 + C (t : ℂ)

private theorem roots_of_square_add (t r : ℂ) (hr : r ^ 2 = -t) :
    (X ^ 2 + C t : ℂ[X]).roots = {r, -r} := by
  have hfactor : (X ^ 2 + C t : ℂ[X]) = (X - C r) * (X - C (-r)) := by
    have ht : t = -r ^ 2 := by
      calc
        t = -(-t) := by simp
        _ = -(r ^ 2) := by rw [← hr]
    rw [ht]
    simp only [map_neg, map_pow]
    ring
  rw [hfactor, roots_mul]
  · simp
  · exact mul_ne_zero (monic_X_sub_C r).ne_zero (monic_X_sub_C (-r)).ne_zero

private theorem neg_sqrt_sq (t : ℝ) (ht : t < 0) :
    (Real.sqrt (-t) : ℝ) ^ 2 = -t := by
  rw [Real.sq_sqrt]
  linarith

private theorem sqrt_sq (t : ℝ) (ht : 0 ≤ t) :
    (Real.sqrt t : ℝ) ^ 2 = t := by
  exact Real.sq_sqrt ht

private theorem complex_I_sqrt_sq (t : ℝ) (ht : 0 ≤ t) :
    ((Complex.I * (Real.sqrt t : ℂ)) ^ 2) = -(t : ℂ) := by
  have hs : (Real.sqrt t : ℝ) ^ 2 = t := sqrt_sq t ht
  apply Complex.ext
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith [hs]
  · norm_num [Complex.mul_re, Complex.mul_im, pow_two]

/-- The explicit `z^2+t` collision model: negative `t` has two distinct real
roots, zero has a double root, and positive `t` has a conjugate pair. -/
theorem quadratic_collision_model_certificate (t : ℝ) :
    (t < 0 →
      (quadraticCollisionPolynomial t).roots =
          {((Real.sqrt (-t) : ℝ) : ℂ), -((Real.sqrt (-t) : ℝ) : ℂ)} ∧
        ((Real.sqrt (-t) : ℝ) : ℂ) ≠ -((Real.sqrt (-t) : ℝ) : ℂ)) ∧
    (t = 0 → (quadraticCollisionPolynomial t).roots = ({0, 0} : Multiset ℂ)) ∧
    (0 < t →
      (quadraticCollisionPolynomial t).roots =
          {Complex.I * (Real.sqrt t : ℂ), -(Complex.I * (Real.sqrt t : ℂ))} ∧
        conj (Complex.I * (Real.sqrt t : ℂ)) =
          -(Complex.I * (Real.sqrt t : ℂ))) := by
  constructor
  · intro ht
    have hs : ((Real.sqrt (-t) : ℝ) : ℂ) ^ 2 = -((t : ℂ)) := by
      exact_mod_cast neg_sqrt_sq t ht
    have hroots := roots_of_square_add (t := (t : ℂ))
      (r := ((Real.sqrt (-t) : ℝ) : ℂ)) hs
    constructor
    · simpa [quadraticCollisionPolynomial] using hroots
    · intro hzero
      have hspos : 0 < Real.sqrt (-t) := Real.sqrt_pos.2 (by linarith)
      have hreal : Real.sqrt (-t) = -Real.sqrt (-t) := by
        exact_mod_cast hzero
      nlinarith [Real.sqrt_pos.2 (by linarith : 0 < -t)]
  · constructor
    · intro ht
      have hroots := roots_of_square_add (t := (0 : ℂ)) (r := (0 : ℂ)) (by norm_num)
      simpa [quadraticCollisionPolynomial, ht] using hroots
    · intro ht
      have hroots := roots_of_square_add (t := (t : ℂ))
        (r := Complex.I * (Real.sqrt t : ℂ)) (complex_I_sqrt_sq t (le_of_lt ht))
      constructor
      · simpa [quadraticCollisionPolynomial] using hroots
      · apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

/- The root multiset has two entries even at the collision, where both entries
are the same zero. -/
theorem off_line_zeros_born_in_pairs_not_created :
    ∀ t : ℝ, (quadraticCollisionPolynomial t).roots.card = 2 := by
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [(quadratic_collision_model_certificate t).1 ht |>.1]
    norm_num
  · rw [(quadratic_collision_model_certificate 0).2.1 rfl]
    norm_num
  · rw [(quadratic_collision_model_certificate t).2.2 ht |>.1]
    norm_num

/- Concrete witnesses make every regime and the universal parameter domain
machine-checkably inhabited. -/
example : (-1 : ℝ) < 0 := by norm_num
example : (0 : ℝ) = 0 := rfl
example : (0 : ℝ) < 1 := by norm_num
example : Nonempty ℝ := ⟨0⟩

/- The third residue names a contour and two three-point spectra, but the
authoritative atom text does not provide those points or bounds. It is therefore
left open rather than instantiated with invented data. -/

end D5.S3.Zeros.ToySpectrum.QuadraticCollisionModel
