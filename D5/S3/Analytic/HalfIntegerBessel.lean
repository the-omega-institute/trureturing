/- GID: D5/S3/Analytic/HalfIntegerBessel
   generality: G
   mirror-B: D5/B/S3/Analytic/HalfIntegerBessel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex half-integer modified Bessel carriers and their Wronskians. -/
module

public import D5.S3.Analytic.HalfIntegerBesselPolynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Complex half-integer modified Bessel carriers

These are the finite carriers of order `m + 1/2` using the principal square root.
Their analytic identities use the open right half-plane.
-/

public section

open Polynomial
open scoped Topology
open D5.S3.Analytic.HalfIntegerBesselPolynomial (carrier)

namespace D5.S3.Analytic.HalfIntegerBessel

/-- The common normalization, with the principal square root of the argument. -/
noncomputable def prefactor (z : ℂ) : ℂ :=
  (Real.sqrt (Real.pi / 2) : ℂ) / Complex.sqrt z

/-- The decaying finite carrier of order `m + 1/2`. -/
noncomputable def K (m : ℕ) (z : ℂ) : ℂ :=
  prefactor z * Complex.exp (-z) * aeval z⁻¹ (carrier m)

/-- The growing reflected finite carrier of order `m + 1/2`. -/
noncomputable def L (m : ℕ) (z : ℂ) : ℂ :=
  prefactor z * Complex.exp z * aeval z⁻¹ ((carrier m).comp (-X))

/-- The regular finite carrier of order `m + 1/2`. -/
noncomputable def I (m : ℕ) (z : ℂ) : ℂ :=
  (L m z - (-1 : ℂ)^m * K m z) / (Real.pi : ℂ)

private theorem arg_ne_zero {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  rintro rfl
  exact (lt_irrefl 0) hz

private theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)

private theorem hasDerivAt_prefactor {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt prefactor (-prefactor z / (2 * z)) z := by
  have hz0 := arg_ne_zero hz
  have hs := sqrt_sq z
  have hs0 : Complex.sqrt z ≠ 0 := by
    intro h
    exact hz0 (by simpa [h] using hs.symm)
  have hroot := Complex.hasDerivAt_sqrt (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  rw [show (-1 / 2 : ℂ) = -(2⁻¹) by norm_num, Complex.cpow_neg] at hroot
  have h := (hasDerivAt_const z (Real.sqrt (Real.pi / 2) : ℂ)).div hroot hs0
  refine h.congr_deriv ?_
  change (0 * Complex.sqrt z - (Real.sqrt (Real.pi / 2) : ℂ) *
      ((Complex.sqrt z)⁻¹ / 2)) / Complex.sqrt z ^ 2 = -prefactor z / (2 * z)
  rw [hs]
  unfold prefactor
  ring

private theorem hasDerivAt_reciprocal (p : ℚ[X]) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun t : ℂ => aeval t⁻¹ p) (-(z⁻¹)^2 * aeval z⁻¹ p.derivative) z := by
  refine ((p.hasDerivAt_aeval (z⁻¹)).comp z (hasDerivAt_inv hz)).congr_deriv ?_
  rw [inv_pow, mul_comm]

/-- Complex derivative of the decaying carrier on the open right half-plane. -/
theorem hasDerivAt_K (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (K m) (prefactor z * Complex.exp (-z) *
      (-(1 + (2 * z)⁻¹) * aeval z⁻¹ (carrier m) -
        z⁻¹ ^ 2 * aeval z⁻¹ (carrier m).derivative)) z := by
  have hexp := (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg
  have h := ((hasDerivAt_prefactor hz).mul hexp).mul
    (hasDerivAt_reciprocal (carrier m) (arg_ne_zero hz))
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Pi.mul_apply, div_eq_mul_inv]
  ring

/-- Complex derivative of the reflected carrier on the open right half-plane. -/
theorem hasDerivAt_L (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    let q := (carrier m).comp (-X)
    HasDerivAt (L m) (prefactor z * Complex.exp z *
      ((1 - (2 * z)⁻¹) * aeval z⁻¹ q - z⁻¹ ^ 2 * aeval z⁻¹ q.derivative)) z := by
  have h := ((hasDerivAt_prefactor hz).mul (Complex.hasDerivAt_exp z)).mul
    (hasDerivAt_reciprocal ((carrier m).comp (-X)) (arg_ne_zero hz))
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, div_eq_mul_inv]
  ring

/-- Complex derivative of the regular carrier on the open right half-plane. -/
theorem hasDerivAt_I (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (I m) ((deriv (L m) z - (-1 : ℂ)^m * deriv (K m) z) / (Real.pi : ℂ)) z :=
  (((hasDerivAt_L m hz).differentiableAt.hasDerivAt).sub
    ((hasDerivAt_K m hz).differentiableAt.hasDerivAt.const_mul ((-1 : ℂ)^m))).div_const _

/-- The common normalization gives the positive Wronskian constant `π`. -/
theorem wronskian_KL (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    z * (K m z * deriv (L m) z - deriv (K m) z * L m z) = (Real.pi : ℂ) := by
  let p := carrier m
  let q := p.comp (-X)
  have hpoly : 2 * aeval z⁻¹ p * aeval z⁻¹ q -
      z⁻¹ ^ 2 * (aeval z⁻¹ p * aeval z⁻¹ q.derivative -
        aeval z⁻¹ p.derivative * aeval z⁻¹ q) = (2 : ℂ) := by
    simpa [p, q] using congrArg (aeval (R := ℚ) z⁻¹)
      (HalfIntegerBesselPolynomial.reflected_wronskian m)
  have hexp : Complex.exp (-z) * Complex.exp z = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hs : z * prefactor z ^ 2 * 2 = (Real.pi : ℂ) := by
    have hc : (Real.sqrt (Real.pi / 2) : ℂ) ^ 2 = (Real.pi : ℂ) / 2 := by
      exact_mod_cast Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity)
    rw [prefactor, div_pow, sqrt_sq z, hc]
    field_simp [arg_ne_zero hz]
  rw [(hasDerivAt_K m hz).deriv, (hasDerivAt_L m hz).deriv, K, L]
  change z * (prefactor z * Complex.exp (-z) * aeval z⁻¹ p *
      (prefactor z * Complex.exp z * ((1 - (2 * z)⁻¹) * aeval z⁻¹ q -
        z⁻¹ ^ 2 * aeval z⁻¹ q.derivative)) -
      prefactor z * Complex.exp (-z) * (-(1 + (2 * z)⁻¹) * aeval z⁻¹ p -
        z⁻¹ ^ 2 * aeval z⁻¹ p.derivative) *
      (prefactor z * Complex.exp z * aeval z⁻¹ q)) = _
  calc
    _ = z * prefactor z ^ 2 * (Complex.exp (-z) * Complex.exp z) *
        (2 * aeval z⁻¹ p * aeval z⁻¹ q -
          z⁻¹ ^ 2 * (aeval z⁻¹ p * aeval z⁻¹ q.derivative -
            aeval z⁻¹ p.derivative * aeval z⁻¹ q)) := by ring
    _ = _ := by rw [hexp, mul_one, hpoly, hs]

/-- The Wronskian in the orientation `K I' − K' I` is `1/z`. -/
theorem wronskian_KI (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    K m z * deriv (I m) z - deriv (K m) z * I m z = 1 / z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := wronskian_KL m hz
  rw [(hasDerivAt_I m hz).deriv, I]
  calc
    _ = (K m z * deriv (L m) z - deriv (K m) z * L m z) / (Real.pi : ℂ) := by
      ring
    _ = 1 / z := by
      field_simp [hpi, arg_ne_zero hz]
      linear_combination h

/-- The ordinary modified Bessel equation for the decaying finite carrier. -/
theorem hasDerivAt_deriv_K (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (deriv (K m))
      ((1 + ((m : ℂ) + 1 / 2)^2 / z^2) * K m z - deriv (K m) z / z) z := by
  let p := carrier m
  let amplitude (t : ℂ) := prefactor t * Complex.exp (-t)
  let slope (t : ℂ) := -(1 + (2 * t)⁻¹)
  let polynomial (t : ℂ) := aeval t⁻¹ p
  let polynomial' (t : ℂ) := aeval t⁻¹ p.derivative
  let polynomial'' (t : ℂ) := aeval t⁻¹ p.derivative.derivative
  have hz0 := arg_ne_zero hz
  have hrecip := hasDerivAt_inv hz0
  have hslope : HasDerivAt slope (z⁻¹ ^ 2 / 2) z := by
    have h := ((hasDerivAt_const z (1 : ℂ)).add (hrecip.div_const (2 : ℂ))).neg
    have hs : slope = (fun t : ℂ => -(1 + t⁻¹ / 2)) := by
      funext t
      simp only [slope, mul_inv_rev, div_eq_mul_inv]
    rw [hs]
    refine h.congr_deriv ?_
    simp only [inv_pow, div_eq_mul_inv]
    ring
  have hamplitude : HasDerivAt amplitude (amplitude z * slope z) z := by
    have hexp := (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg
    refine ((hasDerivAt_prefactor hz).mul hexp).congr_deriv ?_
    simp only [amplitude, slope, Function.comp_apply, div_eq_mul_inv]
    ring
  have hpolynomial := hasDerivAt_reciprocal p hz0
  have hpolynomial' := hasDerivAt_reciprocal p.derivative hz0
  have hderiv := hamplitude.mul
    ((hslope.mul hpolynomial).sub ((hrecip.pow 2).mul hpolynomial'))
  have hevent : ∀ᶠ t in 𝓝 z, 0 < t.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hformula : (deriv (K m)) =ᶠ[𝓝 z]
      (fun t => amplitude t * (slope t * polynomial t - t⁻¹ ^ 2 * polynomial' t)) :=
    hevent.mono fun _ ht => (hasDerivAt_K m ht).deriv
  have hpoly : z⁻¹ ^ 2 * polynomial'' z + (2 * z⁻¹ + 2) * polynomial' z =
      (m : ℂ) * (m + 1) * polynomial z := by
    simpa [polynomial, polynomial', polynomial'', p] using
      congrArg (aeval (R := ℚ) z⁻¹) (HalfIntegerBesselPolynomial.carrier_ode m)
  refine (hderiv.congr_of_eventuallyEq hformula).congr_deriv ?_
  rw [(hasDerivAt_K m hz).deriv]
  change (amplitude z * slope z *
      (slope z * polynomial z - z⁻¹ ^ 2 * polynomial' z) +
      amplitude z * ((z⁻¹ ^ 2 / 2 * polynomial z + slope z *
        (-z⁻¹ ^ 2 * polynomial' z)) -
        ((2 : ℕ) * z⁻¹ ^ (2 - 1) * (-(z ^ 2)⁻¹) * polynomial' z +
          z⁻¹ ^ 2 * (-z⁻¹ ^ 2 * polynomial'' z)))) =
      (1 + ((m : ℂ) + 1 / 2)^2 / z^2) * (amplitude z * polynomial z) -
        amplitude z * (slope z * polynomial z - z⁻¹ ^ 2 * polynomial' z) / z
  simp only [slope, Nat.reduceSub, Nat.cast_ofNat, pow_one, inv_pow, div_eq_mul_inv]
  linear_combination (amplitude z * z⁻¹ ^ 2) * hpoly

end D5.S3.Analytic.HalfIntegerBessel
