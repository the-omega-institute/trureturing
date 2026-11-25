/- GID: D5/S3/Analytic/HalfIntegerBessel
   generality: G
   mirror-B: D5/B/S3/Analytic/HalfIntegerBessel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Half-integer Bessel carriers and their Liouville–Green equation. -/
module

public import D5.S3.Analytic.HalfIntegerBesselPolynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
@[expose] noncomputable def prefactor (z : ℂ) : ℂ :=
  (Real.sqrt (Real.pi / 2) : ℂ) / Complex.sqrt z

/-- The decaying finite carrier of order `m + 1/2`. -/
noncomputable def K (m : ℕ) (z : ℂ) : ℂ :=
  prefactor z * Complex.exp (-z) * aeval z⁻¹ (carrier m)

/-- The growing reflected finite carrier of order `m + 1/2`. -/
@[expose] noncomputable def L (m : ℕ) (z : ℂ) : ℂ :=
  prefactor z * Complex.exp z * aeval z⁻¹ ((carrier m).comp (-X))

/-- The regular finite carrier of order `m + 1/2`. -/
@[expose] noncomputable def I (m : ℕ) (z : ℂ) : ℂ :=
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

section LiouvilleGreen

/-- The positive real order used to scale the carrier argument. -/
noncomputable def order (m : ℕ) : ℝ := (m : ℝ) + 1 / 2

/-- The principal square root in the Liouville–Green change of variable. -/
noncomputable def S (w : ℂ) : ℂ := Complex.sqrt (1 + w ^ 2)

/-- The Liouville–Green phase on the right half-plane. -/
noncomputable def eta (w : ℂ) : ℂ := S w + Complex.log w - Complex.log (1 + S w)

private theorem order_pos (m : ℕ) : 0 < order m := by
  unfold order
  positivity

private theorem one_add_sq_mem_slitPlane {w : ℂ} (hw : 0 < w.re) :
    1 + w ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : w.im = 0
  · left
    simp only [pow_two, Complex.add_re, Complex.one_re, Complex.mul_re, him, mul_zero, sub_zero]
    positivity
  · right
    simp only [pow_two, Complex.add_im, Complex.one_im, zero_add, Complex.mul_im]
    rw [show w.re * w.im + w.im * w.re = 2 * w.re * w.im by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hw.ne') him

private theorem sqrt_re_pos_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hz), Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have hlow := Complex.neg_pi_lt_arg z
  have hhigh := lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hz)
  simp only [Complex.mul_im, Complex.log_im]
  norm_num
  constructor <;> linarith

/-- The phase root stays in the open right half-plane. -/
theorem S_re_pos {w : ℂ} (hw : 0 < w.re) : 0 < (S w).re :=
  sqrt_re_pos_of_mem_slitPlane (one_add_sq_mem_slitPlane hw)

private theorem one_add_S_re_pos {w : ℂ} (hw : 0 < w.re) : 0 < (1 + S w).re := by
  simpa only [Complex.add_re, Complex.one_re] using add_pos zero_lt_one (S_re_pos hw)

private theorem S_sq (w : ℂ) : S w ^ 2 = 1 + w ^ 2 := sqrt_sq _

private theorem hasDerivAt_principalSqrt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt Complex.sqrt (1 / (2 * Complex.sqrt z)) z := by
  have h := Complex.hasDerivAt_sqrt hz
  rw [show (-1 / 2 : ℂ) = -(2⁻¹) by norm_num, Complex.cpow_neg] at h
  refine h.congr_deriv ?_
  change (Complex.sqrt z)⁻¹ / 2 = 1 / (2 * Complex.sqrt z)
  ring

private theorem hasDerivAt_S {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt S (w / S w) w := by
  have harg : HasDerivAt (fun t : ℂ => 1 + t ^ 2) (2 * w) w := by
    simpa using ((hasDerivAt_id w).pow 2).const_add 1
  refine ((hasDerivAt_principalSqrt (one_add_sq_mem_slitPlane hw)).comp w harg).congr_deriv ?_
  change 1 / (2 * S w) * (2 * w) = w / S w
  ring

private theorem log_div_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x / y) = Complex.log x - Complex.log y := by
  have hy0 := arg_ne_zero hy
  have hxarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hyarg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have hyarg' : y.arg ≠ Real.pi := Complex.slitPlane_arg_ne_pi
    (Complex.mem_slitPlane_iff.mpr (Or.inl hy))
  rw [div_eq_mul_inv, Complex.log_mul (arg_ne_zero hx) (inv_ne_zero hy0), Complex.log_inv _ hyarg',
    sub_eq_add_neg]
  rw [Complex.arg_inv, ite_eq_right hyarg']
  exact ⟨by linarith [hxarg.1, hyarg.2], by linarith [hxarg.2, hyarg.1]⟩

/-- The principal logarithms in the phase combine to the logarithm of the quotient. -/
theorem eta_eq_log_div {w : ℂ} (hw : 0 < w.re) :
    eta w = S w + Complex.log (w / (1 + S w)) := by
  rw [eta, log_div_of_re_pos hw (one_add_S_re_pos hw)]
  ring

/-- The phase derivative is the principal-root factor divided by the argument. -/
theorem hasDerivAt_eta {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt eta (S w / w) w := by
  have hs := hasDerivAt_S hw
  have hlog := Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have hlog' := (Complex.hasDerivAt_log
    (Complex.mem_slitPlane_iff.mpr (Or.inl (one_add_S_re_pos hw)))).comp w (hs.const_add 1)
  refine ((hs.add hlog).sub hlog').congr_deriv ?_
  change w / S w + w⁻¹ - (1 + S w)⁻¹ * (w / S w) = S w / w
  field_simp [arg_ne_zero hw, arg_ne_zero (S_re_pos hw), arg_ne_zero (one_add_S_re_pos hw)]
  linear_combination -(S w) * S_sq w

/-- Positive real scaling factors out of the principal square root on the right half-plane. -/
theorem sqrt_real_mul {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 < w.re) :
    Complex.sqrt ((a : ℂ) * w) = (Real.sqrt a : ℂ) * Complex.sqrt w := by
  have hr : 0 < ((Real.sqrt a : ℂ) * Complex.sqrt w).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (Real.sqrt_pos.mpr ha)
      (sqrt_re_pos_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hw)))
  have hs : ((Real.sqrt a : ℂ) * Complex.sqrt w) ^ 2 = (a : ℂ) * w := by
    rw [mul_pow, sqrt_sq, ← Complex.ofReal_pow, Real.sq_sqrt ha.le]
  rw [← hs]
  exact Complex.sq_cpow_two_inv hr

/-- The normalized decaying amplitude in the phase variable. -/
noncomputable def F_K (m : ℕ) (w : ℂ) : ℂ :=
  (Real.sqrt (2 * order m / Real.pi) : ℂ) * Complex.sqrt (S w) *
    Complex.exp ((order m : ℂ) * eta w) * K m ((order m : ℂ) * w)

/-- The normalized decaying amplitude with the positive real scaling canceled. -/
theorem F_K_eq_carrier (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    F_K m w = (Complex.sqrt (S w) / Complex.sqrt w) *
      Complex.exp ((order m : ℂ) * (eta w - w)) *
      aeval (((order m : ℂ) * w)⁻¹) (carrier m) := by
  have hν := order_pos m
  have hνsqrt : (Real.sqrt (order m) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hν).ne'
  have hnorm : (Real.sqrt (2 * order m / Real.pi) : ℂ) * (Real.sqrt (Real.pi / 2) : ℂ) =
      (Real.sqrt (order m) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp [Real.pi_ne_zero]
  rw [F_K, K, prefactor, sqrt_real_mul hν hw, mul_sub, Complex.exp_sub]
  simp only [div_eq_mul_inv, Complex.exp_neg]
  rw [mul_inv_rev (Real.sqrt (order m) : ℂ) (Complex.sqrt w)]
  calc
    _ = ((Real.sqrt (2 * order m / Real.pi) : ℂ) * (Real.sqrt (Real.pi / 2) : ℂ)) *
        (Real.sqrt (order m) : ℂ)⁻¹ *
        ((Complex.sqrt (S w) * (Complex.sqrt w)⁻¹) *
          (Complex.exp ((order m : ℂ) * eta w) * (Complex.exp ((order m : ℂ) * w))⁻¹) *
          aeval (((order m : ℂ) * w)⁻¹) (carrier m)) := by ring_nf
    _ = _ := by rw [hnorm, mul_inv_cancel₀ hνsqrt, one_mul]

/-- Differentiation in the Liouville–Green phase variable. -/
noncomputable def D (f : ℂ → ℂ) (w : ℂ) : ℂ := (w / S w) * deriv f w

/-- The rational potential in the transformed equation. -/
noncomputable def psi (w : ℂ) : ℂ :=
  w ^ 2 * (4 - w ^ 2) / (4 * (1 + w ^ 2) ^ 3)

private theorem hasDerivAt_phaseFactor {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (fun z : ℂ => z / S z) (1 / S w ^ 3) w := by
  have hs := arg_ne_zero (S_re_pos hw)
  refine ((hasDerivAt_id w).div (hasDerivAt_S hw) hs).congr_deriv ?_
  change (1 * S w - w * (w / S w)) / S w ^ 2 = 1 / S w ^ 3
  field_simp [hs]
  linear_combination S_sq w

private theorem hasDerivAt_sqrtS {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (fun z => Complex.sqrt (S z))
      (Complex.sqrt (S w) * (w / (2 * (1 + w ^ 2)))) w := by
  have hs := arg_ne_zero (S_re_pos hw)
  have hsqrt : Complex.sqrt (S w) ≠ 0 := by
    intro h
    exact hs (by simpa [h] using (sqrt_sq (S w)).symm)
  have h := hasDerivAt_principalSqrt (Complex.mem_slitPlane_iff.mpr (Or.inl (S_re_pos hw)))
  refine (h.comp w (hasDerivAt_S hw)).congr_deriv ?_
  change 1 / (2 * Complex.sqrt (S w)) * (w / S w) = _
  rw [← S_sq w]
  field_simp [hs, hsqrt]
  linear_combination -w * sqrt_sq (S w)

private theorem hasDerivAt_sqrtSlope {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (fun z : ℂ => z / (2 * (1 + z ^ 2)))
      ((1 - w ^ 2) / (2 * (1 + w ^ 2) ^ 2)) w := by
  have hA := Complex.slitPlane_ne_zero (one_add_sq_mem_slitPlane hw)
  have harg : HasDerivAt (fun z : ℂ => 2 * (1 + z ^ 2)) (2 * (2 * w)) w := by
    have h : HasDerivAt (fun z : ℂ => 1 + z ^ 2) (2 * w) w := by
      simpa using ((hasDerivAt_id w).pow 2).const_add 1
    exact h.const_mul 2
  refine ((hasDerivAt_id w).div harg (mul_ne_zero (by norm_num) hA)).congr_deriv ?_
  change (1 * (2 * (1 + w ^ 2)) - w * (2 * (2 * w))) / (2 * (1 + w ^ 2)) ^ 2 = _
  field_simp [hA]
  ring

private theorem scaled_re_pos (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    0 < ((order m : ℂ) * w).re := by
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using mul_pos (order_pos m) hw

private theorem hasDerivAt_scaledK (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (fun z => K m ((order m : ℂ) * z))
      (deriv (K m) ((order m : ℂ) * w) * (order m : ℂ)) w := by
  have harg : HasDerivAt (fun z : ℂ => (order m : ℂ) * z) (order m : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul (order m : ℂ)
  exact (hasDerivAt_K m (scaled_re_pos m hw)).differentiableAt.hasDerivAt.comp w harg

private theorem hasDerivAt_scaledK' (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    let y (z : ℂ) := K m ((order m : ℂ) * z)
    HasDerivAt (deriv y)
      (((order m : ℂ) ^ 2 * (1 + w ^ 2) / w ^ 2) * y w - deriv y w / w) w := by
  intro y
  let ν : ℂ := order m
  have hν : ν ≠ 0 := by
    change (order m : ℂ) ≠ 0
    exact_mod_cast (order_pos m).ne'
  have hνcast : (m : ℂ) + 1 / 2 = ν := by
    simp [ν, order]
  have hevent : ∀ᶠ z in 𝓝 w, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hformula : (deriv y) =ᶠ[𝓝 w] (fun z => deriv (K m) (ν * z) * ν) :=
    hevent.mono fun _ hz => (hasDerivAt_scaledK m hz).deriv
  have h := ((hasDerivAt_deriv_K m (scaled_re_pos m hw)).comp w
    ((hasDerivAt_id w).const_mul ν)).mul_const ν
  refine (h.congr_of_eventuallyEq hformula).congr_deriv ?_
  rw [(hasDerivAt_scaledK m hw).deriv]
  simp only [mul_one]
  change ((1 + ((m : ℂ) + 1 / 2) ^ 2 / (ν * w) ^ 2) * y w -
      deriv (K m) (ν * w) / (ν * w)) * ν * ν =
    ν ^ 2 * (1 + w ^ 2) / w ^ 2 * y w - (deriv (K m) (ν * w) * ν) / w
  rw [hνcast]
  field_simp [hν, arg_ne_zero hw]
  ring

private theorem hasDerivAt_sqrtScaledK (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    let y (z : ℂ) := K m ((order m : ℂ) * z)
    let U (z : ℂ) := Complex.sqrt (S z) * y z
    HasDerivAt U (Complex.sqrt (S w) * (deriv y w + w / (2 * (1 + w ^ 2)) * y w)) w := by
  intro y U
  have hy : DifferentiableAt ℂ y w := (hasDerivAt_scaledK m hw).differentiableAt
  refine ((hasDerivAt_sqrtS hw).mul hy.hasDerivAt).congr_deriv ?_
  change Complex.sqrt (S w) * (w / (2 * (1 + w ^ 2))) * y w +
    Complex.sqrt (S w) * deriv y w = _
  ring

private theorem hasDerivAt_D_sqrtScaledK (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    let U (z : ℂ) := Complex.sqrt (S z) * K m ((order m : ℂ) * z)
    HasDerivAt (D U) ((S w / w) * (((order m : ℂ) ^ 2 + psi w) * U w)) w := by
  intro U
  let ν : ℂ := order m
  let y (z : ℂ) := K m (ν * z)
  let a (z : ℂ) := Complex.sqrt (S z)
  let b (z : ℂ) := z / (2 * (1 + z ^ 2))
  let c (z : ℂ) := z / S z
  have hy : HasDerivAt y (deriv y w) w := (hasDerivAt_scaledK m hw).differentiableAt.hasDerivAt
  have hy' : HasDerivAt (deriv y)
      (ν ^ 2 * (1 + w ^ 2) / w ^ 2 * y w - deriv y w / w) w :=
    hasDerivAt_scaledK' m hw
  have ha : HasDerivAt a (a w * b w) w := hasDerivAt_sqrtS hw
  have hb : HasDerivAt b ((1 - w ^ 2) / (2 * (1 + w ^ 2) ^ 2)) w := hasDerivAt_sqrtSlope hw
  have hc : HasDerivAt c (1 / S w ^ 3) w := hasDerivAt_phaseFactor hw
  have hevent : ∀ᶠ z in 𝓝 w, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hformula : D U =ᶠ[𝓝 w] (fun z => c z * a z * (deriv y z + b z * y z)) := by
    filter_upwards [hevent] with z hz
    change c z * deriv U z = _
    rw [(hasDerivAt_sqrtScaledK m hz).deriv]
    change c z * (a z * (deriv y z + b z * y z)) = _
    rw [mul_assoc]
  have h := (hc.mul ha).mul (hy'.add (hb.mul hy))
  refine (h.congr_of_eventuallyEq hformula).congr_deriv ?_
  change (1 / S w ^ 3 * a w + c w * (a w * b w)) * (deriv y w + b w * y w) +
    c w * a w * (ν ^ 2 * (1 + w ^ 2) / w ^ 2 * y w - deriv y w / w +
      ((1 - w ^ 2) / (2 * (1 + w ^ 2) ^ 2) * y w + b w * deriv y w)) = _
  have hs := arg_ne_zero (S_re_pos hw)
  have hw0 := arg_ne_zero hw
  have hfirst : 1 / S w ^ 3 + 2 * c w * b w - c w / w = 0 := by
    dsimp [b, c]
    rw [← S_sq w]
    field_simp [hs, hw0]
    linear_combination -(S_sq w)
  have hzero : (1 / S w ^ 3 + c w * b w) * b w +
      c w * (ν ^ 2 * (1 + w ^ 2) / w ^ 2 + (1 - w ^ 2) / (2 * (1 + w ^ 2) ^ 2)) =
      S w / w * (ν ^ 2 + psi w) := by
    dsimp [b, c, psi]
    rw [← S_sq w]
    field_simp [hs, hw0]
    ring
  change _ = S w / w * ((ν ^ 2 + psi w) * (a w * y w))
  linear_combination a w * deriv y w * hfirst + a w * y w * hzero

private theorem hasDerivAt_D_F_K (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (D (F_K m))
      (S w / w * (2 * (order m : ℂ) * D (F_K m) w + psi w * F_K m w)) w := by
  let ν : ℂ := order m
  let U (z : ℂ) := Complex.sqrt (S z) * K m (ν * z)
  let E (z : ℂ) := (Real.sqrt (2 * order m / Real.pi) : ℂ) * Complex.exp (ν * eta z)
  have hF (z : ℂ) : F_K m z = E z * U z := by
    unfold F_K E U ν
    ring
  have hE (z : ℂ) (hz : 0 < z.re) : HasDerivAt E (E z * ν * (S z / z)) z := by
    have h := ((Complex.hasDerivAt_exp (ν * eta z)).comp z
      ((hasDerivAt_eta hz).const_mul ν)).const_mul (Real.sqrt (2 * order m / Real.pi) : ℂ)
    refine h.congr_deriv ?_
    dsimp only [Function.comp_apply, E]
    ring
  have hU (z : ℂ) (hz : 0 < z.re) : HasDerivAt U (deriv U z) z :=
    (hasDerivAt_sqrtScaledK m hz).differentiableAt.hasDerivAt
  have hdF (z : ℂ) (hz : 0 < z.re) : D (F_K m) z = E z * (D U z + ν * U z) := by
    have h := (hE z hz).mul (hU z hz)
    have heq : F_K m = E * U := funext hF
    unfold D
    rw [heq, h.deriv]
    field_simp [arg_ne_zero hz, arg_ne_zero (S_re_pos hz)]
    ring
  have hUne (z : ℂ) (hz : 0 < z.re) : deriv U z = S z / z * D U z := by
    unfold D
    field_simp [arg_ne_zero hz, arg_ne_zero (S_re_pos hz)]
  have hevent : ∀ᶠ z in 𝓝 w, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hformula : D (F_K m) =ᶠ[𝓝 w] (fun z => E z * (D U z + ν * U z)) :=
    hevent.mono hdF
  have h := (hE w hw).mul ((hasDerivAt_D_sqrtScaledK m hw).add ((hU w hw).const_mul ν))
  refine (h.congr_of_eventuallyEq hformula).congr_deriv ?_
  rw [hdF w hw, hF w, hUne w hw]
  change E w * ν * (S w / w) * (D U w + ν * U w) +
    E w * (S w / w * ((ν ^ 2 + psi w) * U w) + ν * (S w / w * D U w)) = _
  ring

/-- The scaled decaying carrier solves the Liouville–Green equation on the right half-plane. -/
theorem liouvilleGreen_K (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    D (D (F_K m)) w - 2 * (order m : ℂ) * D (F_K m) w = psi w * F_K m w := by
  change w / S w * deriv (D (F_K m)) w - 2 * (order m : ℂ) * D (F_K m) w = _
  rw [(hasDerivAt_D_F_K m hw).deriv]
  field_simp [arg_ne_zero hw, arg_ne_zero (S_re_pos hw)]
  ring

end LiouvilleGreen

end D5.S3.Analytic.HalfIntegerBessel
