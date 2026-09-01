/- GID: D5/S3/Analytic/Boundary/LogNormDirectionalDerivative
   generality: G
   mirror-B: D5/B/S3/Analytic/Boundary/LogNormDirectionalDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The log-norm derivative is the real part of the directional
     logarithmic derivative. -/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/- Library-search audit trail (2026-09-01):
   * Repository searches for `logAbs`, `harmonic`, `logDeriv`,
     `Complex.log`, `InteriorCurvature`, and `XiLogDeriv` found no frozen
     owner for the local derivative of the logarithmic norm in an arbitrary
     complex direction. `InteriorCurvatureCriterion` and
     `OffLineCurvatureDipole` concern atomic curvature measures and reflected
     logarithmic distance potentials, respectively, rather than this local
     Cauchy--Riemann identity.
   * Pinned Mathlib supplies `HasDerivAt.comp_ofReal`,
     `HasDerivAt.norm_sq`, `Real.hasDerivAt_log`, `Real.log_pow`, and
     `Complex.div_re`. They are applied directly below. `Complex.log` is not
     used because its derivative theorem is restricted to a slit plane,
     whereas the logarithmic norm is differentiable at every nonzero value.
   * Searches across the other installed Lean packages found no theorem
     packaging this directional logarithmic-norm derivative. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Boundary.LogNormDirectionalDerivative

/-- Along the real parameterization of an affine complex line, the derivative
of `log ‖f‖` is the real part of the directional logarithmic derivative. The
nonvanishing hypothesis is essential. -/
theorem log_norm_affine_direction_hasDerivAt
    (f : ℂ → ℂ) (f' z v : ℂ) (t : ℝ)
    (hf : HasDerivAt f f' (z + (t : ℂ) * v))
    (hzero : f (z + (t : ℂ) * v) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖f (z + (u : ℂ) * v)‖)
      (v * f' / f (z + (t : ℂ) * v)).re t := by
  let w := f (z + (t : ℂ) * v)
  let q := v * f'
  have hline :
      HasDerivAt (fun u : ℂ => z + u * v) v (t : ℂ) := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (x := (t : ℂ))).mul_const v).const_add z
  have hpathComplex :
      HasDerivAt (fun u : ℂ => f (z + u * v)) q (t : ℂ) := by
    convert! hf.comp (t : ℂ) hline using 1 <;>
      simp only [Function.comp_apply, q, mul_comm]
  have hpath :
      HasDerivAt (fun u : ℝ => f (z + (u : ℂ) * v)) q t := by
    simpa only using hpathComplex.comp_ofReal
  have hnormSqZero : ‖w‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hzero)
  have hlogSq :
      HasDerivAt
        (fun u : ℝ => Real.log (‖f (z + (u : ℂ) * v)‖ ^ 2))
        ((2 * inner ℝ w q) / (‖w‖ ^ 2)) t := by
    simpa only [w] using hpath.norm_sq.log hnormSqZero
  have hhalf := hlogSq.div_const 2
  have hfunctions :
      (fun u : ℝ => Real.log (‖f (z + (u : ℂ) * v)‖ ^ 2) / 2) =
        (fun u : ℝ => Real.log ‖f (z + (u : ℂ) * v)‖) := by
    funext u
    rw [Real.log_pow]
    norm_num
  rw [hfunctions] at hhalf
  have hnormSqNe : Complex.normSq w ≠ 0 := by
    intro h
    exact hzero (Complex.normSq_eq_zero.mp h)
  have hderivative :
      ((2 * inner ℝ w q) / (‖w‖ ^ 2)) / 2 = (q / w).re := by
    rw [Complex.inner, Complex.div_re, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      mul_neg, sub_neg_eq_add]
    field_simp [hnormSqNe]
  rw [hderivative] at hhalf
  simpa only [w, q] using hhalf

/-- For the rotated completed coordinate
`Xi(z) = xi(1/2 - i z)`, changing the upper-half-plane height changes the
argument of `xi` in the positive real direction. Hence the derivative is the
real part of `xi'/xi`. -/
theorem riesz_potential_real_direction_hasDerivAt
    (xi : ℂ → ℂ) (xi' : ℂ) (x omega : ℝ)
    (hxi : HasDerivAt xi xi'
      ((1 : ℂ) / 2 + (omega : ℂ) - Complex.I * (x : ℂ)))
    (hzero : xi
      ((1 : ℂ) / 2 + (omega : ℂ) - Complex.I * (x : ℂ)) ≠ 0) :
    let Xi := fun z : ℂ => xi ((1 : ℂ) / 2 - Complex.I * z)
    HasDerivAt
      (fun u : ℝ => Real.log ‖Xi ((x : ℂ) + Complex.I * (u : ℂ))‖)
      (xi' / xi
        ((1 : ℂ) / 2 + (omega : ℂ) - Complex.I * (x : ℂ))).re omega := by
  dsimp only
  have hpoint :
      ((1 : ℂ) / 2 - Complex.I * (x : ℂ)) + (omega : ℂ) * 1 =
        (1 : ℂ) / 2 + (omega : ℂ) - Complex.I * (x : ℂ) := by
    ring
  have h := log_norm_affine_direction_hasDerivAt
    xi xi' ((1 : ℂ) / 2 - Complex.I * (x : ℂ)) 1 omega
    (by rw [hpoint]; exact hxi)
    (by rw [hpoint]; exact hzero)
  rw [hpoint] at h
  simp only [one_mul] at h
  convert h using 1
  · funext u
    ring_nf
    rw [Complex.I_sq]
    ring

/-- In the unrotated coordinate `x + i*omega`, the height derivative is the
negative imaginary part of the logarithmic derivative, not its real part. -/
theorem vertical_log_norm_hasDerivAt
    (f : ℂ → ℂ) (f' : ℂ) (x omega : ℝ)
    (hf : HasDerivAt f f' ((x : ℂ) + Complex.I * (omega : ℂ)))
    (hzero : f ((x : ℂ) + Complex.I * (omega : ℂ)) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖f ((x : ℂ) + Complex.I * (u : ℂ))‖)
      (-(f' / f ((x : ℂ) + Complex.I * (omega : ℂ))).im) omega := by
  have hpoint :
      (x : ℂ) + (omega : ℂ) * Complex.I =
        (x : ℂ) + Complex.I * (omega : ℂ) := by
    ring
  have h := log_norm_affine_direction_hasDerivAt
    f f' (x : ℂ) Complex.I omega
    (by rw [hpoint]; exact hf)
    (by rw [hpoint]; exact hzero)
  rw [hpoint] at h
  convert h using 1
  · funext u
    congr 2
    ring
  · simp [div_eq_mul_inv, mul_assoc]

/-- A zero at `1/2 + delta + i*gamma` rotates to
`-gamma + i*delta`; positive `delta` puts it in the upper half-plane. -/
theorem off_line_zero_rotates_to_upper_half_plane
    (xi : ℂ → ℂ) (delta gamma : ℝ) (hdelta : 0 < delta)
    (hzero : xi
      ((1 : ℂ) / 2 + (delta : ℂ) + Complex.I * (gamma : ℂ)) = 0) :
    let Xi := fun z : ℂ => xi ((1 : ℂ) / 2 - Complex.I * z)
    let zrho := (-gamma : ℂ) + Complex.I * (delta : ℂ)
    Xi zrho = 0 ∧ zrho.im = delta ∧ 0 < zrho.im := by
  dsimp only
  have hcoordinate :
      (1 : ℂ) / 2 - Complex.I *
          ((-gamma : ℂ) + Complex.I * (delta : ℂ)) =
        (1 : ℂ) / 2 + (delta : ℂ) + Complex.I * (gamma : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  constructor
  · rw [hcoordinate]
    exact hzero
  · simp [hdelta]

private theorem identity_vertical_example :
    HasDerivAt
        (fun omega : ℝ =>
          Real.log ‖(1 : ℂ) + Complex.I * (omega : ℂ)‖)
        ((1 : ℝ) / 2) 1 ∧
      ((1 : ℂ) / ((1 : ℂ) + Complex.I)).re = (1 : ℝ) / 2 := by
  constructor
  · have h := vertical_log_norm_hasDerivAt
      (fun z : ℂ => z) 1 1 1
      (by simpa using (hasDerivAt_id' (x := (1 : ℂ) + Complex.I)))
      (by
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre)
    convert h using 1 <;>
      norm_num [Complex.div_im, Complex.normSq_apply, pow_two,
        Complex.mul_re, Complex.mul_im]
  · norm_num [Complex.div_re, Complex.normSq_apply]

private theorem square_vertical_example :
    HasDerivAt
        (fun omega : ℝ =>
          Real.log ‖((1 : ℂ) + Complex.I * (omega : ℂ)) ^ 2‖)
        1 1 ∧
      ((2 : ℂ) / ((1 : ℂ) + Complex.I)).re = 1 := by
  have hsquare :
      HasDerivAt (fun z : ℂ => z ^ 2)
        (2 * ((1 : ℂ) + Complex.I)) ((1 : ℂ) + Complex.I) := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hasDerivAt_pow 2 ((1 : ℂ) + Complex.I))
  constructor
  · have h := vertical_log_norm_hasDerivAt
      (fun z : ℂ => z ^ 2) (2 * ((1 : ℂ) + Complex.I)) 1 1
      (by simpa using hsquare)
      (by
        apply pow_ne_zero 2
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre)
    convert h using 1 <;>
      norm_num [Complex.div_im, Complex.normSq_apply, pow_two,
        Complex.mul_re, Complex.mul_im]
  · norm_num [Complex.div_re, Complex.normSq_apply]

#print axioms log_norm_affine_direction_hasDerivAt
#print axioms riesz_potential_real_direction_hasDerivAt
#print axioms vertical_log_norm_hasDerivAt
#print axioms off_line_zero_rotates_to_upper_half_plane
#print axioms identity_vertical_example
#print axioms square_vertical_example

end D5.S3.Analytic.Boundary.LogNormDirectionalDerivative
