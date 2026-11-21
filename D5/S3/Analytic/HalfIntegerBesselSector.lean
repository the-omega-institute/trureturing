/- GID: D5/S3/Analytic/HalfIntegerBesselSector
   generality: G
   mirror-B: D5/B/S3/Analytic/HalfIntegerBesselSector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Radial Volterra bounds for the decaying and regular half-integer Bessel amplitudes. -/
module

public import D5.S3.Analytic.HalfIntegerBessel
import all D5.S3.Analytic.HalfIntegerBessel
public import D5.S3.Analytic.HalfIntegerBesselPolynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import D5.S3.Analytic.RadialVolterra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Sector bounds for the half-integer Bessel amplitudes

Radial integration controls the normalized decaying and regular amplitudes on right half-plane sectors.
-/

public section

open Polynomial
open scoped Topology
open D5.S3.Analytic.HalfIntegerBesselPolynomial (carrier)

namespace D5.S3.Analytic.HalfIntegerBessel

section LiouvilleGreen

/-- The phase derivative along the real radius on a fixed ray. -/
noncomputable def radialP (u : ℂ) (r : ℝ) : ℂ := S ((r : ℂ) * u) / (r : ℂ)

/-- The coefficient of the amplitude in the radial equation for its phase derivative. -/
noncomputable def radialQ (u : ℂ) (r : ℝ) : ℂ := radialP u r * psi ((r : ℂ) * u)

private theorem ray_re_pos {u : ℂ} (hu : 0 < u.re) {r : ℝ} (hr : 0 < r) :
    0 < ((r : ℂ) * u).re := by
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    using mul_pos hr hu

private theorem radialP_re_pos {u : ℂ} (hu : 0 < u.re) {r : ℝ} (hr : 0 < r) :
    0 < (radialP u r).re := by
  have hS := S_re_pos (ray_re_pos hu hr)
  simp only [radialP, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_ofReal, mul_zero]
  positivity

/-- On a ray, the phase and the normalized decaying amplitude satisfy the radial Volterra system. -/
theorem radialSystem_K (m : ℕ) {u : ℂ} (hu : 0 < u.re) {r : ℝ} (hr : 0 < r) :
    let phase (t : ℝ) := eta ((t : ℂ) * u)
    let F (t : ℝ) := F_K m ((t : ℂ) * u)
    let G (t : ℝ) := D (F_K m) ((t : ℂ) * u)
    HasDerivAt phase (radialP u r) r ∧
    HasDerivAt F (radialP u r * G r) r ∧
    HasDerivAt G (2 * (order m : ℂ) * radialP u r * G r + radialQ u r * F r) r ∧
    0 < (radialP u r).re := by
  intro phase F G
  let w := (r : ℂ) * u
  have hw : 0 < w.re := ray_re_pos hu hr
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hu0 := arg_ne_zero hu
  have hS0 := arg_ne_zero (S_re_pos hw)
  have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u r := by
    simpa using (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt.mul_const u
  have hF : DifferentiableAt ℂ (F_K m) w := by
    unfold F_K
    have hE := (Complex.hasDerivAt_exp ((order m : ℂ) * eta w)).comp w
      ((hasDerivAt_eta hw).const_mul (order m : ℂ))
    exact (((hasDerivAt_sqrtS hw).const_mul (Real.sqrt (2 * order m / Real.pi) : ℂ)).mul
      hE |>.mul (hasDerivAt_scaledK m hw)).differentiableAt
  have hp : (S w / w) * u = radialP u r := by
    dsimp [w, radialP]
    field_simp [hr0, hu0]
  have hphase : HasDerivAt phase (u * (S w / w)) r := by
    change HasDerivAt (eta ∘ fun t : ℝ => (t : ℂ) * u) (u • (S w / w)) r
    exact (hasDerivAt_eta hw).scomp r harg
  refine ⟨hphase.congr_deriv (by rwa [mul_comm u]), ?_, ?_, radialP_re_pos hu hr⟩
  · refine (hF.hasDerivAt.scomp r harg).congr_deriv ?_
    change u * deriv (F_K m) w = radialP u r * (w / S w * deriv (F_K m) w)
    rw [← hp]
    field_simp [arg_ne_zero hw, hS0]
  · refine ((hasDerivAt_D_F_K m hw).scomp r harg).congr_deriv ?_
    change u * ((S w / w) * (2 * (order m : ℂ) * G r + psi w * F r)) =
      2 * (order m : ℂ) * radialP u r * G r + radialP u r * psi w * F r
    rw [← hp]
    ring

private theorem ray_norm {u : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r : ℂ) * u‖ = r := by
  rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

/-- The phase root on a unit ray makes at most the angle of the ray with the positive axis. -/
theorem radial_S_re_ge {u : ℂ} (hu : ‖u‖ = 1) (hure : 0 < u.re) {r : ℝ} (hr : 0 < r) :
    u.re * ‖S ((r : ℂ) * u)‖ ≤ (S ((r : ℂ) * u)).re := by
  let w := (r : ℂ) * u
  let A := 1 + w ^ 2
  let c := (u ^ 2).re
  have hS : 0 < (S w).re := S_re_pos (ray_re_pos hure hr)
  have hc : 2 * u.re ^ 2 = 1 + c := by
    have hn : u.re ^ 2 + u.im ^ 2 = 1 := by
      rw [pow_two, pow_two, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hu, one_pow]
    dsimp [c]
    simp only [pow_two, Complex.mul_re]
    nlinarith
  have hwnorm : ‖w ^ 2‖ = r ^ 2 := by rw [norm_pow, show ‖w‖ = r from ray_norm hu hr.le]
  have hAle : ‖A‖ ≤ 1 + r ^ 2 := by
    exact (norm_add_le (1 : ℂ) (w ^ 2)).trans_eq (by rw [norm_one, hwnorm])
  have hAge : r ^ 2 - 1 ≤ ‖A‖ := by
    have h := norm_sub_norm_le (w ^ 2) (-1 : ℂ)
    rw [hwnorm, norm_neg, norm_one, sub_neg_eq_add, add_comm] at h
    exact h
  have hAre : A.re = 1 + r ^ 2 * c := by
    dsimp [A, w, c]
    rw [mul_pow]
    simp [← Complex.ofReal_pow, Complex.mul_re]
  have hA : c * ‖A‖ ≤ A.re := by
    rw [hAre]
    by_cases h : 0 ≤ c
    · have hc1 : c ≤ 1 := by
        exact (Complex.re_le_norm _).trans_eq (by rw [norm_pow, hu, one_pow])
      calc
        _ ≤ c * (1 + r ^ 2) := mul_le_mul_of_nonneg_left hAle h
        _ ≤ _ := by linarith
    · have hc1 : -1 ≤ c := by
        have hbound := Complex.abs_re_le_norm (u ^ 2)
        rw [norm_pow, hu, one_pow] at hbound
        exact (abs_le.mp hbound).1
      calc
        _ ≤ c * (r ^ 2 - 1) := mul_le_mul_of_nonpos_left hAge (le_of_not_ge h)
        _ ≤ _ := by linarith
  have hSre : 2 * (S w).re ^ 2 = ‖A‖ + A.re := by
    have hn : ‖A‖ = ‖S w‖ ^ 2 := by rw [show A = S w ^ 2 from (S_sq w).symm, norm_pow]
    rw [hn, Complex.sq_norm, Complex.normSq_apply, show A.re = ((S w) ^ 2).re from
      congrArg Complex.re (S_sq w).symm]
    simp only [pow_two, Complex.mul_re]
    ring
  have hSnorm : ‖S w‖ ^ 2 = ‖A‖ := by
    rw [show A = S w ^ 2 from (S_sq w).symm, norm_pow]
  change u.re * ‖S w‖ ≤ (S w).re
  apply (sq_le_sq₀ (mul_nonneg hure.le (norm_nonneg _)) hS.le).mp
  rw [mul_pow, hSnorm]
  nlinarith only [hSre, hA, congrArg (fun x => x * ‖A‖) hc]

private theorem radial_A_norm_ge {κ : ℝ} {u : ℂ} (hu : ‖u‖ = 1) (hsector : κ ≤ u.re)
    (r : ℝ) : κ * (1 + r ^ 2) ≤ ‖1 + ((r : ℂ) * u) ^ 2‖ := by
  let A := 1 + ((r : ℂ) * u) ^ 2
  have hunit : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    simp
  have heq : A * (starRingEnd ℂ) u = (starRingEnd ℂ) u + (r : ℂ) ^ 2 * u := by
    dsimp only [A]
    rw [add_mul, mul_pow]
    linear_combination ((r : ℂ) ^ 2 * u) * hunit
  have hre : (A * (starRingEnd ℂ) u).re = (1 + r ^ 2) * u.re := by
    rw [heq]
    simp [← Complex.ofReal_pow, Complex.add_re, Complex.mul_re, add_mul]
  have hbound := Complex.re_le_norm (A * (starRingEnd ℂ) u)
  rw [hre, norm_mul, Complex.norm_conj, hu, mul_one] at hbound
  exact (by
    rw [mul_comm κ]
    exact (mul_le_mul_of_nonneg_left hsector (by positivity)).trans hbound)

/-- An integrable real majorant for the radial potential on sectors of positive aperture. -/
noncomputable def sectorMajorant (κ r : ℝ) : ℝ :=
  r * (4 + r ^ 2) / (4 * ((Real.sqrt κ) ^ 5 * (Real.sqrt (1 + r ^ 2)) ^ 5))

/-- Pointwise majorization of the complex radial potential on the closed sector. -/
theorem norm_radialQ_le {κ : ℝ} (hκ : 0 < κ) {u : ℂ} (hu : ‖u‖ = 1)
    (hsector : κ ≤ u.re) {r : ℝ} (hr : 0 < r) :
    ‖radialQ u r‖ ≤ sectorMajorant κ r := by
  let w := (r : ℂ) * u
  let s := ‖S w‖
  let d := Real.sqrt κ * Real.sqrt (1 + r ^ 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : 0 < s := norm_pos_iff.mpr (arg_ne_zero (S_re_pos (ray_re_pos (hκ.trans_le hsector) hr)))
  have hsq : s ^ 2 = ‖1 + w ^ 2‖ := by rw [← S_sq w, norm_pow]
  have hd_le : d ≤ s := by
    apply (sq_le_sq₀ hd.le hs.le).mp
    dsimp only [d]
    rw [mul_pow, Real.sq_sqrt hκ.le, Real.sq_sqrt (by positivity), hsq]
    exact radial_A_norm_ge hu hsector r
  have h4 : ‖(4 : ℂ) - w ^ 2‖ ≤ 4 + r ^ 2 := by
    have h := norm_sub_le (4 : ℂ) (w ^ 2)
    rw [norm_pow, show ‖w‖ = r from ray_norm hu hr.le] at h
    norm_num at h ⊢
    exact h
  have hq : ‖radialQ u r‖ = r * ‖(4 : ℂ) - w ^ 2‖ / (4 * s ^ 5) := by
    change ‖(S w / (r : ℂ)) * (w ^ 2 * (4 - w ^ 2) / (4 * (1 + w ^ 2) ^ 3))‖ = _
    rw [norm_mul, norm_div, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, ← hsq,
      ray_norm hu hr.le, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hfour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
    rw [hfour]
    field_simp [hr.ne', hs.ne']
    change s * ‖(4 : ℂ) - w ^ 2‖ = ‖(4 : ℂ) - w ^ 2‖ * s
    exact mul_comm _ _
  have hmajor : sectorMajorant κ r = r * (4 + r ^ 2) / (4 * d ^ 5) := by
    rw [sectorMajorant, show d ^ 5 =
      (Real.sqrt κ) ^ 5 * (Real.sqrt (1 + r ^ 2)) ^ 5 from mul_pow ..]
  rw [hq, hmajor]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hd_le 5) (by norm_num))
    |>.trans' (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hr.le)
      (by positivity))

private theorem continuous_sectorMajorant {κ : ℝ} (hκ : 0 < κ) :
    Continuous (sectorMajorant κ) := by
  unfold sectorMajorant
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro r
    positivity

/-- The full positive radial interval gives mass at most (1/(2\kappa^{5/2})). -/
theorem sectorMajorant_mass {κ : ℝ} (hκ : 0 < κ) {a b : ℝ} :
    (∫ r in a..b, sectorMajorant κ r) ≤ 1 / (2 * (Real.sqrt κ) ^ 5) := by
  let B (r : ℝ) := Real.sqrt (1 + r ^ 2)
  let c := 4 * (Real.sqrt κ) ^ 5
  let T (r : ℝ) := ((B r)⁻¹ + ((B r)⁻¹) ^ 3) / c
  have hc : 0 < c := by dsimp [c]; positivity
  have hB (r : ℝ) : 0 < B r := by dsimp [B]; positivity
  have hB2 (r : ℝ) : B r ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
  have hd (r : ℝ) : HasDerivAt (fun t => -T t) (sectorMajorant κ r) r := by
    have harg : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * r) r := by
      simpa using ((hasDerivAt_id r).pow 2).const_add 1
    have hroot : HasDerivAt B (r / B r) r := by
      have h := (Real.hasDerivAt_sqrt (show (1 + r ^ 2 : ℝ) ≠ 0 by positivity)).comp r harg
      refine h.congr_deriv ?_
      change 1 / (2 * B r) * (2 * r) = r / B r
      ring
    have hinv := hroot.inv (hB r).ne'
    have h := ((hinv.add (hinv.pow 3)).div_const c).neg
    refine h.congr_deriv ?_
    simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.inv_apply, sectorMajorant]
    change -((-(r / B r) / B r ^ 2 + 3 * (B r)⁻¹ ^ 2 * (-(r / B r) / B r ^ 2)) / c) =
      r * (4 + r ^ 2) / (4 * ((Real.sqrt κ) ^ 5 * B r ^ 5))
    rw [show (4 : ℝ) * ((Real.sqrt κ) ^ 5 * B r ^ 5) = c * B r ^ 5 by dsimp [c]; ring]
    field_simp [(hB r).ne', hc.ne']
    linear_combination r * hB2 r
  have hint : IntervalIntegrable (sectorMajorant κ) MeasureTheory.volume a b :=
    (continuous_sectorMajorant hκ).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hint]
  have hTb : 0 ≤ T b := by dsimp [T]; positivity
  have hBa : 1 ≤ B a := by
    have h : 1 ≤ 1 + a ^ 2 := by nlinarith [sq_nonneg a]
    simpa only [B, Real.sqrt_one] using Real.sqrt_le_sqrt h
  have hi : (B a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBa
  have hi3 : ((B a)⁻¹) ^ 3 ≤ 1 := pow_le_one₀ (by positivity) hi
  calc
    -T b - -T a ≤ T a := by linarith
    _ ≤ 2 / c := div_le_div_of_nonneg_right (by linarith) hc.le
    _ = 1 / (2 * (Real.sqrt κ) ^ 5) := by dsimp [c]; ring

private theorem S_zero : S 0 = 1 := by simp [S, Complex.sqrt]

private theorem div_re_pos_of_im_mul_nonneg {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re)
    (him : 0 ≤ x.im * y.im) : 0 < (x / y).re := by
  rw [Complex.div_re, ← add_div]
  exact div_pos (add_pos_of_pos_of_nonneg (mul_pos hx hy) him)
    (Complex.normSq_pos.mpr (arg_ne_zero hy))

private theorem S_im_mul_nonneg {w : ℂ} (hw : 0 < w.re) : 0 ≤ (S w).im * w.im := by
  have hS := S_re_pos hw
  have heq := congrArg Complex.im (S_sq w)
  simp only [pow_two, Complex.add_im, Complex.one_im, zero_add, Complex.mul_im] at heq
  have him : (S w).im * w.im = (w.re / (S w).re) * w.im ^ 2 := by
    field_simp [hS.ne']
    linear_combination (w.im / 2) * heq
  rw [him]
  positivity

private theorem S_div_eq_inv {w : ℂ} (hw : 0 < w.re) : S w / w = S w⁻¹ := by
  have hw0 := arg_ne_zero hw
  have hpos := div_re_pos_of_im_mul_nonneg (S_re_pos hw) hw (S_im_mul_nonneg hw)
  have hs : (S w / w) ^ 2 = 1 + (w⁻¹) ^ 2 := by
    rw [div_pow, S_sq w]
    field_simp [hw0]
    exact add_comm _ _
  change S w / w = Complex.sqrt (1 + (w⁻¹) ^ 2)
  rw [← hs]
  exact (Complex.sq_cpow_two_inv hpos).symm

private theorem sqrtS_div_eq_inv {w : ℂ} (hw : 0 < w.re) :
    Complex.sqrt (S w) / Complex.sqrt w = Complex.sqrt (S w⁻¹) := by
  let a := Complex.sqrt (S w)
  let b := Complex.sqrt w
  have ha : 0 < a.re := sqrt_re_pos_of_mem_slitPlane
    (Complex.mem_slitPlane_iff.mpr (Or.inl (S_re_pos hw)))
  have hb : 0 < b.re := sqrt_re_pos_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hw))
  have hsa : a ^ 2 = S w := sqrt_sq _
  have hsb : b ^ 2 = w := sqrt_sq _
  have hima : (S w).im = 2 * a.re * a.im := by
    rw [← hsa, pow_two, Complex.mul_im]
    ring
  have himb : w.im = 2 * b.re * b.im := by
    rw [← hsb, pow_two, Complex.mul_im]
    ring
  have him := S_im_mul_nonneg hw
  rw [hima, himb, show 2 * a.re * a.im * (2 * b.re * b.im) =
    (4 * a.re * b.re) * (a.im * b.im) by ring] at him
  have hab := div_re_pos_of_im_mul_nonneg ha hb
    (nonneg_of_mul_nonneg_right him (by positivity))
  have hsq : (a / b) ^ 2 = S w⁻¹ := by rw [div_pow, hsa, hsb, S_div_eq_inv hw]
  change a / b = Complex.sqrt (S w⁻¹)
  rw [← hsq]
  exact (Complex.sq_cpow_two_inv hab).symm

private theorem eta_sub_eq_inv {w : ℂ} (hw : 0 < w.re) :
    eta w - w = w⁻¹ / (1 + S w⁻¹) - Complex.log (w⁻¹ + S w⁻¹) := by
  have hS := S_div_eq_inv hw
  have hw0 := arg_ne_zero hw
  have hT : 0 < (S w⁻¹).re := by
    rw [← hS]
    exact div_re_pos_of_im_mul_nonneg (S_re_pos hw) hw (S_im_mul_nonneg hw)
  have hone := arg_ne_zero (show 0 < (1 + S w⁻¹).re by
    simpa only [Complex.add_re, Complex.one_re] using add_pos zero_lt_one hT)
  have hdiff : S w - w = w⁻¹ / (1 + S w⁻¹) := by
    apply (eq_div_iff hone).mpr
    rw [← hS]
    field_simp [hw0]
    linear_combination S_sq w
  have hquot : (1 + S w) / w = w⁻¹ + S w⁻¹ := by rw [add_div, one_div, hS]
  rw [eta, ← hquot, log_div_of_re_pos (one_add_S_re_pos hw) hw, ← hdiff]
  ring

/-- The normalized amplitude in the reciprocal coordinate at the terminal endpoint. -/
private noncomputable def terminalAmplitude (m : ℕ) (v : ℂ) : ℂ :=
  Complex.sqrt (S v) *
    Complex.exp ((order m : ℂ) * (v / (1 + S v) - Complex.log (v + S v))) *
    aeval (v / (order m : ℂ)) (carrier m)

private theorem F_K_eq_terminalAmplitude (m : ℕ) {w : ℂ} (hw : 0 < w.re) :
    F_K m w = terminalAmplitude m w⁻¹ := by
  rw [F_K_eq_carrier m hw, terminalAmplitude, sqrtS_div_eq_inv hw, eta_sub_eq_inv hw,
    mul_inv_rev]
  simp only [div_eq_mul_inv]

private theorem terminalAmplitude_zero (m : ℕ) : terminalAmplitude m 0 = 1 := by
  simp [terminalAmplitude, S_zero, Complex.sqrt, aeval_def, eval₂_at_zero,
    HalfIntegerBesselPolynomial.carrier_coeff_zero]

private theorem terminalAmplitude_analyticAt (m : ℕ) :
    AnalyticAt ℂ (terminalAmplitude m) 0 := by
  have hv : AnalyticAt ℂ (fun v : ℂ => v) 0 := analyticAt_id
  have hs : AnalyticAt ℂ S 0 := by
    unfold S Complex.sqrt
    apply (analyticAt_const.add (hv.pow 2)).cpow analyticAt_const
    simp
  have hsqrt : AnalyticAt ℂ (fun v => Complex.sqrt (S v)) 0 := by
    unfold Complex.sqrt
    exact hs.cpow analyticAt_const (by simp [S_zero])
  have hdiv : AnalyticAt ℂ (fun v : ℂ => v / (1 + S v)) 0 :=
    hv.div (analyticAt_const.add hs) (by simp [S_zero])
  have hlog : AnalyticAt ℂ (fun v : ℂ => Complex.log (v + S v)) 0 :=
    (hv.add hs).clog (by simp [S_zero])
  have he : AnalyticAt ℂ (fun v : ℂ =>
      Complex.exp ((order m : ℂ) * (v / (1 + S v) - Complex.log (v + S v)))) 0 :=
    (analyticAt_const.mul (hdiv.sub hlog)).cexp
  have hp : AnalyticAt ℂ (fun v : ℂ => aeval (v / (order m : ℂ)) (carrier m)) 0 := by
    have hpol (v : ℂ) :
        aeval v (carrier m) = (Polynomial.map (algebraMap ℚ ℂ) (carrier m)).eval v :=
      (aeval_def _ _).trans (eval_map _ _).symm
    simp_rw [hpol]
    have hp : Differentiable ℂ (fun v : ℂ =>
        ((carrier m).map (algebraMap ℚ ℂ)).eval v) :=
      fun v => (((carrier m).map (algebraMap ℚ ℂ)).hasDerivAt v).differentiableAt
    exact (hp.analyticAt _).comp (hv.div_const (c := (order m : ℂ)))
  exact (hsqrt.mul he).mul hp

private theorem D_F_K_eq_terminalAmplitude_deriv (m : ℕ) {w : ℂ} (hw : 0 < w.re)
    (han : AnalyticAt ℂ (terminalAmplitude m) w⁻¹) :
    D (F_K m) w = -(w⁻¹ ^ 2 / S w⁻¹) * deriv (terminalAmplitude m) w⁻¹ := by
  have hw0 := arg_ne_zero hw
  have hevent : ∀ᶠ z in 𝓝 w, 0 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw
  have hformula : F_K m =ᶠ[𝓝 w] (fun z => terminalAmplitude m z⁻¹) :=
    hevent.mono fun _ hz => F_K_eq_terminalAmplitude m hz
  have h := han.differentiableAt.hasDerivAt.comp w (hasDerivAt_inv hw0)
  unfold D
  rw [(h.congr_of_eventuallyEq hformula).deriv, ← S_div_eq_inv hw]
  field_simp [hw0, arg_ne_zero (S_re_pos hw)]

/-- Both terminal values for the decaying amplitude hold along each right-half-plane ray. -/
theorem radial_K_terminal (m : ℕ) {u : ℂ} (hu : 0 < u.re) :
    Filter.Tendsto (fun r : ℝ => F_K m ((r : ℂ) * u)) Filter.atTop (𝓝 1) ∧
    Filter.Tendsto (fun r : ℝ => D (F_K m) ((r : ℂ) * u)) Filter.atTop (𝓝 0) := by
  let v (r : ℝ) := ((r : ℂ) * u)⁻¹
  have hv : Filter.Tendsto v Filter.atTop (𝓝 0) := by
    have hr : Filter.Tendsto (fun r : ℝ => ((r⁻¹ : ℝ) : ℂ)) Filter.atTop (𝓝 0) := by
      simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero : Filter.Tendsto (Inv.inv : ℝ → ℝ) Filter.atTop (𝓝 0))
    simpa [v, mul_inv_rev, Complex.ofReal_inv] using hr.const_mul u⁻¹
  have hright : ∀ᶠ r : ℝ in Filter.atTop, 0 < ((r : ℂ) * u).re :=
    (Filter.eventually_gt_atTop 0).mono fun _ hr => ray_re_pos hu hr
  have ha := terminalAmplitude_analyticAt m
  constructor
  · have ht := ha.continuousAt.tendsto.comp hv
    rw [terminalAmplitude_zero] at ht
    exact ht.congr' (hright.mono fun _ hw => (F_K_eq_terminalAmplitude m hw).symm)
  · have hS : ContinuousAt S (0 : ℂ) := by
      have harg : ContinuousAt (fun v : ℂ => 1 + v ^ 2) 0 := by fun_prop
      have hroot : ContinuousAt Complex.sqrt (1 : ℂ) :=
        Complex.continuousAt_sqrt (Or.inl (by norm_num))
      have harg0 : (fun v : ℂ => 1 + v ^ 2) 0 = 1 := by norm_num
      exact hroot.comp_of_eq harg harg0
    have hfactor : Filter.Tendsto (fun v : ℂ => -(v ^ 2 / S v)) (𝓝 0) (𝓝 0) := by
      have hf : ContinuousAt (fun v : ℂ => -(v ^ 2 / S v)) 0 :=
        (((continuous_id.pow 2).continuousAt).div hS (by simp [S_zero])).neg
      simpa [S_zero] using hf.tendsto
    have ht := (hfactor.comp hv).mul (ha.deriv.continuousAt.tendsto.comp hv)
    simp only [zero_mul] at ht
    refine ht.congr' ?_
    have hev := hv.eventually ha.eventually_analyticAt
    filter_upwards [hright, hev] with r hw hlocal
    exact (D_F_K_eq_terminalAmplitude_deriv m hw hlocal).symm

/-- The sector mass bound (V_\kappa=1/(2\kappa^{5/2})). -/
noncomputable def sectorMass (κ : ℝ) : ℝ := 1 / (2 * (Real.sqrt κ) ^ 5)

/-- Uniform Volterra bounds for the decaying amplitude on the whole positive ray. -/
theorem radial_K_bounds (m : ℕ) {κ : ℝ} (hκ : 0 < κ) (hm : sectorMass κ < order m)
    {u : ℂ} (hu : ‖u‖ = 1) (hsector : κ ≤ u.re) {r : ℝ} (hr : 0 < r) :
    ‖F_K m ((r : ℂ) * u)‖ ≤ order m / (order m - sectorMass κ) ∧
    ‖F_K m ((r : ℂ) * u) - 1‖ ≤ sectorMass κ / (order m - sectorMass κ) := by
  have hure := hκ.trans_le hsector
  have hp : ContinuousOn (radialP u) (Set.Ioi 0) := by
    intro t ht
    have htpos : 0 < t := ht
    have harg : ContinuousAt (fun x : ℝ => (x : ℂ) * u) t := by fun_prop
    have hs : ContinuousAt (fun x : ℝ => S ((x : ℂ) * u)) t :=
      ContinuousAt.comp' (f := fun x : ℝ => (x : ℂ) * u)
        (hasDerivAt_S (ray_re_pos hure htpos)).continuousAt harg
    exact (hs.div Complex.continuous_ofReal.continuousAt
      (Complex.ofReal_ne_zero.mpr htpos.ne')).continuousWithinAt
  have hq : ContinuousOn (radialQ u) (Set.Ioi 0) := by
    unfold radialQ
    refine hp.mul ?_
    intro t ht
    have htpos : 0 < t := ht
    have hdenom : 4 * (1 + ((t : ℂ) * u) ^ 2) ^ 3 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero _
        (Complex.slitPlane_ne_zero (one_add_sq_mem_slitPlane (ray_re_pos hure htpos))))
    have hcont : ContinuousAt (fun x : ℝ => psi ((x : ℂ) * u)) t := by
      unfold psi
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hdenom
    exact hcont.continuousWithinAt
  have hsys (s : ℝ) (hs : 0 < s) := radialSystem_K m hure hs
  obtain ⟨hF, hG⟩ := radial_K_terminal m hure
  apply RadialVolterra.norm_bounds (show 0 ≤ sectorMass κ by unfold sectorMass; positivity) hm
    hp hq (fun s hs => (hsys s hs).1) (fun s hs => (hsys s hs).2.1)
    (fun s hs => (hsys s hs).2.2.1) (fun s hs => (hsys s hs).2.2.2.le) hF hG
    (continuous_sectorMajorant hκ).continuousOn
    (fun s hs => by unfold sectorMajorant; positivity)
    (fun s hs => norm_radialQ_le hκ hu hsector hs)
    (fun _ _ _ _ => sectorMajorant_mass hκ) r hr

/-- The decaying amplitude is within the reviewed sector error and the carrier is nonzero. -/
theorem sector_K_estimate (m : ℕ) {κ : ℝ} (hκ : 0 < κ) (hm : 4 * sectorMass κ ≤ order m)
    {w : ℂ} (hw : w ≠ 0) (hsector : κ * ‖w‖ ≤ w.re) :
    ‖F_K m w - 1‖ ≤ 2 * sectorMass κ / order m ∧
    2 * sectorMass κ / order m ≤ 1 / 2 ∧
    K m ((order m : ℂ) * w) ≠ 0 := by
  let r := ‖w‖
  let u := w / (r : ℂ)
  have hr := norm_pos_iff.mpr hw
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hu : ‖u‖ = 1 := by
    change ‖w / (r : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hre : u.re = w.re / r := by
    change (w / (r : ℂ)).re = _
    rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, add_zero,
      Complex.normSq_ofReal]
    field_simp [hr.ne']
  have huκ : κ ≤ u.re := by
    rw [hre, le_div_iff₀ hr]
    exact hsector
  have hwu : (r : ℂ) * u = w := by
    dsimp only [u]
    field_simp [hr0]
  have hV : 0 < sectorMass κ := by unfold sectorMass; positivity
  have hsmall : sectorMass κ < order m := by linarith
  have hb := (radial_K_bounds m hκ hsmall hu huκ hr).2
  rw [hwu] at hb
  have hbound : ‖F_K m w - 1‖ ≤ 2 * sectorMass κ / order m := by
    refine hb.trans ?_
    rw [div_le_div_iff₀ (sub_pos.mpr hsmall) (order_pos m)]
    nlinarith [mul_nonneg hV.le (show 0 ≤ order m - 2 * sectorMass κ by linarith)]
  have hhalf : 2 * sectorMass κ / order m ≤ 1 / 2 := by
    rw [div_le_iff₀ (order_pos m)]
    linarith
  refine ⟨hbound, hhalf, ?_⟩
  intro hk
  have hz : F_K m w = 0 := by simp [F_K, hk]
  have habs := hbound.trans hhalf
  rw [hz, zero_sub, norm_neg, norm_one] at habs
  norm_num at habs

/-- The normalized regular amplitude in the phase variable. -/
noncomputable def F_I (m : ℕ) (w : ℂ) : ℂ :=
  (Real.sqrt (2 * Real.pi * order m) : ℂ) * Complex.sqrt (S w) *
    Complex.exp (-(order m : ℂ) * eta w) * I m ((order m : ℂ) * w)

private theorem sqrt_I_scale (m : ℕ) :
    Real.sqrt (2 * Real.pi * order m) = Real.pi * Real.sqrt (2 * order m / Real.pi) := by
  calc
    _ = Real.sqrt (Real.pi ^ 2 * (2 * order m / Real.pi)) := by
      congr 1
      field_simp [Real.pi_ne_zero]
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq Real.pi_pos.le]

/-- The relative amplitude is the normalized quotient where the decaying carrier is nonzero. -/
theorem F_I_div_F_K (m : ℕ) {w : ℂ} (hw : 0 < w.re)
    (hK : K m ((order m : ℂ) * w) ≠ 0) :
    F_I m w / F_K m w =
      (Real.pi : ℂ) * Complex.exp (-2 * (order m : ℂ) * eta w) *
        (I m ((order m : ℂ) * w) / K m ((order m : ℂ) * w)) := by
  have hS : Complex.sqrt (S w) ≠ 0 := arg_ne_zero
    (sqrt_re_pos_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl (S_re_pos hw))))
  have hN : (Real.sqrt (2 * order m / Real.pi) : ℂ) ≠ 0 := by
    have hp := order_pos m
    exact_mod_cast (show Real.sqrt (2 * order m / Real.pi) ≠ 0 by positivity)
  rw [F_I, F_K, sqrt_I_scale, Complex.ofReal_mul,
    show -2 * (order m : ℂ) * eta w = -((order m : ℂ) * eta w) - (order m : ℂ) * eta w by ring,
    Complex.exp_sub, neg_mul]
  field_simp [hS, hK, hN, Complex.exp_ne_zero]

/-- Reversal replaces the argument by its reciprocal and clears the degree power. -/
theorem reverse_eval (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    aeval z (carrier m).reverse = z ^ m * aeval z⁻¹ (carrier m) := by
  have : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have h := eval₂_reverse_mul_pow (algebraMap ℚ ℂ) z⁻¹ (carrier m)
  rw [invOf_eq_inv, inv_inv, HalfIntegerBesselPolynomial.natDegree_carrier] at h
  simp_rw [aeval_def]
  rw [← h, inv_pow, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero m hz), mul_one]

private theorem regularQuotient_extension (m : ℕ) {z : ℂ} (hz : 0 < z.re)
    (hB : aeval z (carrier m).reverse ≠ 0) :
    I m z / K m z =
      ((-1 : ℂ) ^ m * (Complex.exp (2 * z) * aeval (-z) (carrier m).reverse /
        aeval z (carrier m).reverse - 1)) / (Real.pi : ℂ) := by
  let B : ℂ → ℂ := fun t => aeval t (carrier m).reverse
  have hz0 := arg_ne_zero hz
  have hP : aeval z⁻¹ (carrier m) = B z / z ^ m := by
    apply (eq_div_iff (pow_ne_zero m hz0)).mpr
    change _ = aeval z (carrier m).reverse
    rw [reverse_eval m hz0, mul_comm]
  have hQ : aeval z⁻¹ ((carrier m).comp (-X)) = B (-z) / (-z) ^ m := by
    rw [aeval_comp, map_neg, aeval_X, ← inv_neg]
    apply (eq_div_iff (pow_ne_zero m (neg_ne_zero.mpr hz0))).mpr
    change _ = aeval (-z) (carrier m).reverse
    rw [reverse_eval m (neg_ne_zero.mpr hz0), mul_comm]
  change B z ≠ 0 at hB
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hroot : Complex.sqrt z ≠ 0 := arg_ne_zero
    (sqrt_re_pos_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hz)))
  have hnorm : (Real.sqrt (Real.pi / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (Real.pi / 2) ≠ 0 by positivity)
  have hA : prefactor z ≠ 0 := div_ne_zero hnorm hroot
  have hsign : ((-1 : ℂ) ^ m)⁻¹ = (-1 : ℂ) ^ m := by rw [← inv_pow, inv_neg, inv_one]
  change I m z / K m z = ((-1 : ℂ) ^ m * (Complex.exp (2 * z) * B (-z) / B z - 1)) / _
  have hneg : (-z) ^ m = (-1 : ℂ) ^ m * z ^ m := by rw [← neg_one_mul z, mul_pow]
  rw [I, L, K, hP, hQ, hneg, div_eq_mul_inv (B (-z)), mul_inv_rev, hsign]
  rw [show (2 : ℂ) * z = z - (-z) by ring, Complex.exp_sub]
  field_simp [hπ, hB, hA, hz0, Complex.exp_ne_zero]

/-- The unnormalized quotient of the regular and decaying carriers tends to zero at the origin. -/
theorem radial_I_div_K_zero (m : ℕ) {u : ℂ} (hu : 0 < u.re) :
    Filter.Tendsto (fun r : ℝ => I m ((order m : ℂ) * ((r : ℂ) * u)) /
      K m ((order m : ℂ) * ((r : ℂ) * u))) (𝓝[>] 0) (𝓝 0) := by
  let B (z : ℂ) := aeval z (carrier m).reverse
  let H (z : ℂ) := ((-1 : ℂ)^m * (Complex.exp (2 * z) * B (-z) / B z - 1)) / (Real.pi : ℂ)
  have hB0 : B 0 ≠ 0 := by
    have hp : carrier m ≠ 0 := by
      intro hp
      have hc := HalfIntegerBesselPolynomial.carrier_coeff_zero m
      simp [hp] at hc
    change aeval (0 : ℂ) (carrier m).reverse ≠ 0
    rw [aeval_def, eval₂_at_zero, coeff_zero_reverse]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr (leadingCoeff_ne_zero.mpr hp)
  have hB : Continuous B := continuous_iff_continuousAt.mpr fun z => by
    change ContinuousAt (fun t : ℂ => aeval t (carrier m).reverse) z
    exact ((carrier m).reverse.hasDerivAt_aeval z).continuousAt
  have hH : ContinuousAt H 0 := by
    unfold H
    refine (((ContinuousAt.div (by fun_prop (disch := assumption)) hB.continuousAt hB0).sub
      continuousAt_const).const_mul _).div_const _
  have hH0 : H 0 = 0 := by simp [H, hB0]
  let z (r : ℝ) := (order m : ℂ) * ((r : ℂ) * u)
  have hz0 : z 0 = 0 := by simp [z]
  have hz : Filter.Tendsto z (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt z 0 := by unfold z; fun_prop
    rw [← hz0]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hH.tendsto.comp hz
  rw [hH0] at ht
  refine ht.congr' ?_
  have hBN := hz.eventually (hB.continuousAt.eventually_ne hB0)
  filter_upwards [self_mem_nhdsWithin, hBN] with r hr hb
  exact (regularQuotient_extension m (scaled_re_pos m (ray_re_pos hu hr)) hb).symm

/-- The real part of the phase diverges to negative infinity on each unit ray at the origin. -/
theorem radial_eta_re_atBot {u : ℂ} (hu : ‖u‖ = 1) :
    Filter.Tendsto (fun r : ℝ => (eta ((r : ℂ) * u)).re) (𝓝[>] 0) Filter.atBot := by
  let ray (r : ℝ) := (r : ℂ) * u
  have hS : ContinuousAt (fun r : ℝ => S (ray r)) 0 := by
    have harg : ContinuousAt (fun r : ℝ => 1 + (ray r)^2) 0 := by unfold ray; fun_prop
    have hroot : ContinuousAt Complex.sqrt (1 : ℂ) :=
      Complex.continuousAt_sqrt (Or.inl (by norm_num))
    exact hroot.comp_of_eq harg (by simp [ray])
  have hlog : ContinuousAt (fun r : ℝ => Complex.log (1 + S (ray r))) 0 := by
    have harg : ContinuousAt (fun r : ℝ => 1 + S (ray r)) 0 := continuousAt_const.add hS
    have hroot : ContinuousAt Complex.log (2 : ℂ) := (Complex.hasDerivAt_log
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num)))).continuousAt
    exact hroot.comp_of_eq harg (by norm_num [ray, S_zero])
  have hcor : ContinuousAt (fun r : ℝ => (S (ray r)).re - (Complex.log (1 + S (ray r))).re) 0 :=
    (Complex.continuous_re.continuousAt.comp' hS).sub
      (Complex.continuous_re.continuousAt.comp' hlog)
  have ht := (hcor.tendsto.mono_left nhdsWithin_le_nhds).add_atBot Real.tendsto_log_nhdsGT_zero
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with r hr
  have hn : ‖ray r‖ = r := ray_norm hu (le_of_lt hr)
  change _ = (eta (ray r)).re
  rw [eta, Complex.sub_re, Complex.add_re, Complex.log_re, Complex.log_re, hn]
  ring

private theorem hasDerivAt_radial_I_div_K (m : ℕ) {u : ℂ} (hu : 0 < u.re)
    {s : ℝ} (hs : 0 < s) (hK : K m ((order m : ℂ) * ((s : ℂ) * u)) ≠ 0) :
    HasDerivAt (fun t : ℝ => I m ((order m : ℂ) * ((t : ℂ) * u)) /
      K m ((order m : ℂ) * ((t : ℂ) * u)))
      (1 / ((s : ℂ) * K m ((order m : ℂ) * ((s : ℂ) * u)) ^ 2)) s := by
  let z := (order m : ℂ) * ((s : ℂ) * u)
  have hz := scaled_re_pos m (ray_re_pos hu hs)
  have hz0 : z ≠ 0 := arg_ne_zero hz
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hK0 : K m z ≠ 0 := hK
  have hquot : HasDerivAt (fun w => I m w / K m w) ((1 / z) / K m z ^ 2) z := by
    convert ((hasDerivAt_I m hz).differentiableAt.hasDerivAt.div
      (hasDerivAt_K m hz).differentiableAt.hasDerivAt hK0) using 1
    rw [← wronskian_KI m hz]
    change (K m z * deriv (I m) z - deriv (K m) z * I m z) / K m z ^ 2 =
      (deriv (I m) z * K m z - I m z * deriv (K m) z) / K m z ^ 2
    ring
  have harg : HasDerivAt (fun t : ℝ => (order m : ℂ) * ((t : ℂ) * u))
      ((order m : ℂ) * u) s := by
    simpa using ((Complex.ofRealCLM.hasFDerivAt (x := s)).hasDerivAt.mul_const u).const_mul
      (order m : ℂ)
  refine (hquot.scomp s harg).congr_deriv ?_
  change (order m : ℂ) * u * ((1 / z) / K m z ^ 2) = 1 / ((s : ℂ) * K m z ^ 2)
  field_simp [hz0, hs0, hK0]
  dsimp [z]
  ring

private noncomputable def inwardKernel (m : ℕ) (u : ℂ) (r s : ℝ) : ℂ :=
  Complex.exp (-2 * (order m : ℂ) * (eta ((r : ℂ) * u) - eta ((s : ℂ) * u)))

private noncomputable def radialCorrection (m : ℕ) (u : ℂ) (r s : ℝ) : ℂ :=
  (Real.pi : ℂ) * Complex.exp (-2 * (order m : ℂ) * eta ((r : ℂ) * u)) *
    (I m ((order m : ℂ) * ((s : ℂ) * u)) / K m ((order m : ℂ) * ((s : ℂ) * u))) -
    inwardKernel m u r s

private theorem hasDerivAt_radialCorrection (m : ℕ) {u : ℂ} (hu : 0 < u.re) (r : ℝ)
    {s : ℝ} (hs : 0 < s) (hK : K m ((order m : ℂ) * ((s : ℂ) * u)) ≠ 0) :
    HasDerivAt (radialCorrection m u r)
      (2 * (order m : ℂ) * radialP u s * inwardKernel m u r s *
        ((F_K m ((s : ℂ) * u) ^ 2)⁻¹ - 1)) s := by
  let w := (s : ℂ) * u
  let ν : ℂ := order m
  let φ := eta ((r : ℂ) * u)
  have hν := order_pos m
  have hν0 : ν ≠ 0 := Complex.ofReal_ne_zero.mpr hν.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hS0 : S w ≠ 0 := arg_ne_zero (S_re_pos (ray_re_pos hu hs))
  have hK0 : K m (ν * w) ≠ 0 := hK
  have hF2 : F_K m w ^ 2 =
      (2 * ν / (Real.pi : ℂ)) * S w * Complex.exp (2 * ν * eta w) * K m (ν * w) ^ 2 := by
    have hroot := Real.sq_sqrt (show 0 ≤ 2 * order m / Real.pi by positivity)
    simp only [F_K, mul_pow, sqrt_sq, ← Complex.ofReal_pow, hroot,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    change _ * _ * Complex.exp (ν * eta w) ^ 2 * _ = _
    rw [pow_two (Complex.exp _), ← Complex.exp_add]
    congr 3
    ring
  have hphase := (radialSystem_K m hu hs).1
  have hE : HasDerivAt (inwardKernel m u r)
      (2 * ν * radialP u s * inwardKernel m u r s) s := by
    have hd := (Complex.hasDerivAt_exp (-2 * ν * (φ - eta w))).scomp s
      ((hphase.const_sub φ).const_mul (-2 * ν))
    refine hd.congr_deriv ?_
    change -2 * ν * (-radialP u s) * inwardKernel m u r s = _
    ring
  have hweighted : 2 * ν * radialP u s * inwardKernel m u r s * (F_K m w ^ 2)⁻¹ =
      (Real.pi : ℂ) * Complex.exp (-2 * ν * φ) * (1 / ((s : ℂ) * K m (ν * w) ^ 2)) := by
    change 2 * ν * (S w / (s : ℂ)) * Complex.exp (-2 * ν * (φ - eta w)) * _ = _
    rw [hF2, show -2 * ν * (φ - eta w) = -2 * ν * φ + 2 * ν * eta w by ring, Complex.exp_add]
    field_simp [hν0, hπ, hs0, hS0, hK0, Complex.exp_ne_zero]
  have hd := ((hasDerivAt_radial_I_div_K m hu hs hK).const_mul
    ((Real.pi : ℂ) * Complex.exp (-2 * ν * φ))).sub hE
  refine hd.congr_deriv ?_
  change _ = 2 * ν * radialP u s * inwardKernel m u r s * ((F_K m w ^ 2)⁻¹ - 1)
  rw [mul_sub, mul_one, hweighted]

private theorem norm_ge_half_of_close_to_one {z : ℂ} (h : ‖z - 1‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖z‖ := by
  have htriangle := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one, norm_sub_rev] at htriangle
  linarith

private theorem norm_inv_sq_sub_one_le {z : ℂ} {δ : ℝ} (h : ‖z - 1‖ ≤ δ)
    (hδ : δ ≤ 1 / 2) : ‖(z ^ 2)⁻¹ - 1‖ ≤ 10 * δ := by
  have hδ0 := (norm_nonneg _).trans h
  have hz := norm_ge_half_of_close_to_one (h.trans hδ)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hplus : ‖1 + z‖ ≤ 5 / 2 := by
    have htriangle := norm_add_le (2 : ℂ) (z - 1)
    rw [show (2 : ℂ) + (z - 1) = 1 + z by ring, Complex.norm_two] at htriangle
    linarith
  have hdenom : (1 / 4 : ℝ) ≤ ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) (norm_nonneg z)]
  rw [show (z ^ 2)⁻¹ - 1 = (1 - z) * (1 + z) / z ^ 2 by field_simp [hz0]; ring,
    norm_div, norm_mul, norm_pow, norm_sub_rev (1 : ℂ) z, div_le_iff₀ (by positivity)]
  calc
    ‖z - 1‖ * ‖1 + z‖ ≤ δ * (5 / 2) :=
      mul_le_mul h hplus (norm_nonneg _) hδ0
    _ = (10 * δ) * (1 / 4) := by ring
    _ ≤ (10 * δ) * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_left hdenom (by positivity)

open Filter in
private theorem radialCorrection_zero (m : ℕ) {u : ℂ} (hu : ‖u‖ = 1)
    (hure : 0 < u.re) (r : ℝ) :
    Filter.Tendsto (radialCorrection m u r) (𝓝[>] 0) (𝓝 0) := by
  have hν := order_pos m
  have hE : Filter.Tendsto (inwardKernel m u r) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hshift : Tendsto (fun s : ℝ => -(eta ((r : ℂ) * u)).re + (eta ((s : ℂ) * u)).re)
        (𝓝[>] 0) atBot :=
      tendsto_const_nhds.add_atBot (radial_eta_re_atBot hu)
    have harg := hshift.const_mul_atBot (show 0 < 2 * order m by positivity)
    refine (Real.tendsto_exp_atBot.comp harg).congr fun s => ?_
    simp only [Function.comp_apply, inwardKernel, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.sub_re]
    ring
  unfold radialCorrection
  simpa only [mul_zero, sub_zero] using
    ((radial_I_div_K_zero m hure).const_mul
      ((Real.pi : ℂ) * Complex.exp (-2 * (order m : ℂ) * eta ((r : ℂ) * u)))).sub hE

open Filter Set in
private theorem radial_relative_bound (m : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hm : 4 * sectorMass κ ≤ order m) {u : ℂ} (hu : ‖u‖ = 1) (huκ : κ ≤ u.re)
    {r : ℝ} (hr : 0 < r) :
    ‖F_I m ((r : ℂ) * u) / F_K m ((r : ℂ) * u) - 1‖ ≤
      10 * (2 * sectorMass κ / order m) / κ := by
  let δ := 2 * sectorMass κ / order m
  let C := 10 * δ / κ
  let ν := order m
  let ray (s : ℝ) := (s : ℂ) * u
  let phase (s : ℝ) := eta (ray s)
  let E (s : ℝ) := Real.exp (2 * ν * ((phase s).re - (phase r).re))
  let J := radialCorrection m u r
  let j (s : ℝ) := 2 * (ν : ℂ) * radialP u s * inwardKernel m u r s *
    ((F_K m (ray s) ^ 2)⁻¹ - 1)
  let e (s : ℝ) := 2 * ν * (radialP u s).re * E s
  have hν : 0 < ν := order_pos m
  have hure := hκ.trans_le huκ
  have hsector (s : ℝ) (hs : 0 < s) :=
    sector_K_estimate m hκ hm (arg_ne_zero (ray_re_pos hure hs))
      (show κ * ‖ray s‖ ≤ (ray s).re by
        rw [show ‖ray s‖ = s from ray_norm hu hs.le]
        simpa [ray, Complex.mul_re, mul_comm] using mul_le_mul_of_nonneg_left huκ hs.le)
  have hJ (s : ℝ) (hs : 0 < s) : HasDerivAt J (j s) s :=
    hasDerivAt_radialCorrection m hure r hs (hsector s hs).2.2
  have hE (s : ℝ) (hs : 0 < s) : HasDerivAt E (e s) s := by
    have hd : HasDerivAt (fun t => (phase t).re) (radialP u s).re s :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (radialSystem_K m hure hs).1
    simpa only [mul_comm, e, E, mul_assoc, mul_left_comm] using
      (((hd.sub_const (phase r).re).const_mul (2 * ν)).exp)
  have hkernel (s : ℝ) : ‖inwardKernel m u r s‖ = E s := by
    rw [inwardKernel, Complex.norm_exp]
    congr 1
    simp [ν, phase, ray, Complex.mul_re, Complex.sub_re]
    ring
  have hj_bound (s : ℝ) (hs : 0 < s) : ‖j s‖ ≤ C * e s := by
    have hangle : κ * ‖radialP u s‖ ≤ (radialP u s).re := by
      have ha := (mul_le_mul_of_nonneg_right huκ (norm_nonneg (S (ray s)))).trans
        (radial_S_re_ge hu hure hs)
      have hre : (radialP u s).re = (S (ray s)).re / s := by
        simp [radialP, ray, Complex.div_re, Complex.normSq_ofReal]
        field_simp [hs.ne']
      rw [hre, radialP, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right ha hs.le
    have herror := norm_inv_sq_sub_one_le (hsector s hs).1 (hsector s hs).2.1
    have hδ : 0 ≤ δ := (norm_nonneg _).trans (hsector s hs).1
    have hEpos : 0 < E s := Real.exp_pos _
    have hppos := radialP_re_pos hure hs
    have hp := (le_div_iff₀ hκ).mpr (by rwa [mul_comm] : ‖radialP u s‖ * κ ≤ (radialP u s).re)
    simp only [j, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hν.le, hkernel]
    calc
      2 * ν * ‖radialP u s‖ * E s * ‖(F_K m (ray s) ^ 2)⁻¹ - 1‖
          ≤ 2 * ν * ((radialP u s).re / κ) * E s * (10 * δ) := by gcongr
      _ = C * e s := by dsimp only [C, e]; ring
  have hp_cont (s : ℝ) (hs : 0 < s) : ContinuousAt (radialP u) s := by
    have hray : ContinuousAt ray s := by unfold ray; fun_prop
    have hS : ContinuousAt (fun t => S (ray t)) s :=
      (hasDerivAt_S (ray_re_pos hure hs)).continuousAt.comp' (f := ray) hray
    exact hS.div Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr hs.ne')
  have hj_cont : ContinuousOn j (Ioi 0) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hsys := radialSystem_K m hure hs0
    have hFK := hsys.2.1.continuousAt
    have hF0 : F_K m (ray s) ≠ 0 := norm_pos_iff.mp
      (lt_of_lt_of_le (by norm_num) (norm_ge_half_of_close_to_one
        ((hsector s hs0).1.trans (hsector s hs0).2.1)))
    have hker : ContinuousAt (inwardKernel m u r) s := by
      unfold inwardKernel
      exact Complex.continuous_exp.continuousAt.comp'
        ((continuousAt_const.sub hsys.1.continuousAt).const_mul _)
    exact ((((hp_cont s hs0).const_mul _).mul hker).mul
      (((hFK.pow 2).inv₀ (pow_ne_zero _ hF0)).sub continuousAt_const)).continuousWithinAt
  have he_cont : ContinuousOn (fun s => C * e s) (Ioi 0) := by
    intro s hs
    exact (((Complex.continuous_re.continuousAt.comp' (hp_cont s hs)).const_mul _).mul
      (hE s hs).continuousAt).const_mul _ |>.continuousWithinAt
  have hfinite (a : ℝ) (ha : 0 < a) (har : a ≤ r) : ‖J r - J a‖ ≤ C := by
    have hinterval : uIcc a r ⊆ Ioi (0 : ℝ) := by
      rw [uIcc_of_le har]
      exact fun _ hs => ha.trans_le hs.1
    have hJFTC : (∫ s in a..r, j s) = J r - J a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hJ s (hinterval hs))
        (hj_cont.mono hinterval).intervalIntegrable
    have hEFTC : (∫ s in a..r, C * e s) = C * E r - C * E a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => (hE s (hinterval hs)).const_mul C)
        (he_cont.mono hinterval).intervalIntegrable
    rw [← hJFTC]
    calc
      ‖∫ s in a..r, j s‖ ≤ ∫ s in a..r, C * e s :=
        intervalIntegral.norm_integral_le_of_norm_le har
          (Eventually.of_forall fun s hs => hj_bound s (ha.trans hs.1))
          (he_cont.mono hinterval).intervalIntegrable
      _ = C * E r - C * E a := hEFTC
      _ ≤ C := by
        have hC : 0 ≤ C := by
          have hδ := (norm_nonneg _).trans (hsector r hr).1
          change 0 ≤ δ at hδ
          dsimp only [C]
          positivity
        have hEr : E r = 1 := by simp [E]
        rw [hEr, mul_one]
        exact sub_le_self _ (mul_nonneg hC (Real.exp_pos _).le)
  have hlimit := radialCorrection_zero m hu hure r
  have hclose : ‖J r‖ ≤ C := by
    have ht : Tendsto (fun a => ‖J r - J a‖) (𝓝[>] 0) (𝓝 ‖J r‖) := by
      simpa only [sub_zero] using (hlimit.const_sub (J r)).norm
    apply le_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsGT hr] with a ha
    exact hfinite a ha.1 ha.2.le
  have hJr : J r = F_I m (ray r) / F_K m (ray r) - 1 := by
    rw [F_I_div_F_K m (ray_re_pos hure hr) (hsector r hr).2.2]
    simp [J, radialCorrection, inwardKernel]
  rwa [hJr] at hclose

/-- The regular amplitude and its ratio to the decaying amplitude obey uniform sector bounds. -/
theorem sector_I_estimate (m : ℕ) {κ : ℝ} (hκ : 0 < κ) (hm : 4 * sectorMass κ ≤ order m)
    {w : ℂ} (hw : w ≠ 0) (hsector : κ * ‖w‖ ≤ w.re) :
    let δ := 2 * sectorMass κ / order m
    ‖F_I m w / F_K m w - 1‖ ≤ 10 * δ / κ ∧
      ‖F_I m w - 1‖ ≤ (1 + 15 / κ) * δ := by
  intro δ
  let r := ‖w‖
  let u := w / (r : ℂ)
  have hr := norm_pos_iff.mpr hw
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hu : ‖u‖ = 1 := by
    change ‖w / (r : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne']
  have huκ : κ ≤ u.re := by
    change κ ≤ (w / (r : ℂ)).re
    rw [show (w / (r : ℂ)).re = w.re / r by
      simp [Complex.div_re, Complex.normSq_ofReal]; field_simp [hr.ne'], le_div_iff₀ hr]
    exact hsector
  have hwu : (r : ℂ) * u = w := by
    dsimp only [u]
    field_simp [hr0]
  have hrelative := radial_relative_bound m hκ hm hu huκ hr
  rw [hwu] at hrelative
  obtain ⟨hK, hhalf, _⟩ := sector_K_estimate m hκ hm hw hsector
  have hF0 : F_K m w ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num) (norm_ge_half_of_close_to_one (hK.trans hhalf)))
  have hFupper : ‖F_K m w‖ ≤ 3 / 2 := by
    have htriangle := norm_sub_norm_le (F_K m w) 1
    rw [norm_one] at htriangle
    linarith
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hK
  refine ⟨hrelative, ?_⟩
  rw [show F_I m w - 1 = (F_I m w / F_K m w - 1) * F_K m w + (F_K m w - 1) by
    rw [sub_mul, div_mul_cancel₀ _ hF0, one_mul]
    ring]
  calc
    _ ≤ ‖(F_I m w / F_K m w - 1) * F_K m w‖ + ‖F_K m w - 1‖ := norm_add_le _ _
    _ ≤ (10 * δ / κ) * (3 / 2) + δ := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul hrelative hFupper (norm_nonneg _) (by positivity)) hK
    _ = (1 + 15 / κ) * δ := by ring

end LiouvilleGreen

end D5.S3.Analytic.HalfIntegerBessel
