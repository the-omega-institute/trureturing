/- GID: D5/S3/Zeros/DegreeRoots/EscapeWitness
   generality: G
   mirror-B: D5/B/S3/Zeros/DegreeRoots/EscapeWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative inverse-power sums obey an argument-dependent root bound. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none.
damped_trig_bound: proof_shape: content; escape_witness: damped_trig_bound; consumer: normalized_escape_bound_pos.
term_re: proof_shape: bind-only; escape_witness: none; consumer: inverse_power_re.
escape_mass_bound: proof_shape: bind-only; escape_witness: none; consumer: normalized_escape_bound_pos.
escape_exponent_bound: proof_shape: bind-only; escape_witness: none; consumer: normalized_escape_bound_pos.
inverse_polar: proof_shape: bind-only; escape_witness: none; consumer: inverse_power_re.
inverse_power_re: proof_shape: bind-only; escape_witness: none; consumer: normalized_escape_bound_pos.
normalized_escape_bound_pos: proof_shape: content; escape_witness: damped_trig_bound; consumer: normalized_escape_bound.
normalized_root_arg_ne_zero: proof_shape: bind-only; escape_witness: none; consumer: normalized_escape_bound.
normalized_escape_bound: proof_shape: content; escape_witness: damped_trig_bound; consumer: Result.graph_exterior_bound.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20929
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.DegreeRoots.EscapeWitness

open scoped BigOperators
open Classical

private lemma damped_trig_bound {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    -Real.exp (-lam * Real.pi) ≤ Real.exp (-lam * t) * (Real.cos t + lam * Real.sin t) := by
  by_cases htp : t ≤ Real.pi
  · let q : ℝ → ℝ := fun u => Real.exp (lam * u) *
        (Real.cos u - lam * Real.sin u)
    have hqdiff : Differentiable ℝ q := by
      dsimp [q]
      fun_prop
    have hqderiv (u : ℝ) : deriv q u =
        -(1 + lam ^ 2) * Real.exp (lam * u) * Real.sin u := by
      have hlin : HasDerivAt (fun x : ℝ => lam * x) lam u := by
        exact hasDerivAt_const_mul lam
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (lam * x))
          (lam * Real.exp (lam * u)) u := by
        convert (Real.hasDerivAt_exp (lam * u)).comp u hlin using 1
        · funext x
          rfl
        · ring
      have htrig : HasDerivAt (fun x : ℝ => Real.cos x - lam * Real.sin x)
          (-Real.sin u - lam * Real.cos u) u := by
        convert (Real.hasDerivAt_cos u).sub
          ((hasDerivAt_const u lam).mul (Real.hasDerivAt_sin u)) using 1 <;> ring
      have hqhas := hexp.mul htrig
      have hqhas' : HasDerivAt q
          (-(1 + lam ^ 2) * Real.exp (lam * u) * Real.sin u) u := by
        convert hqhas using 1 <;> ring
      exact hqhas'.deriv
    have hqanti : AntitoneOn q (Set.Icc (0 : ℝ) Real.pi) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 Real.pi)
      · exact hqdiff.continuous.continuousOn
      · exact fun x _ => hqdiff.differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' : x ∈ Set.Ioo (0 : ℝ) Real.pi := by
          simpa only [interior_Icc] using hx
        rw [hqderiv]
        have hs : 0 ≤ Real.sin x :=
          Real.sin_nonneg_of_nonneg_of_le_pi hx'.1.le hx'.2.le
        have hp : 0 ≤ (1 + lam ^ 2) * Real.exp (lam * x) * Real.sin x := by
          positivity
        linarith
    let u : ℝ := Real.pi - t
    have hu : 0 ≤ u := sub_nonneg.mpr htp
    have hup : u ≤ Real.pi := by exact sub_le_self Real.pi ht
    have hqle : q u ≤ q 0 := hqanti ⟨le_rfl, Real.pi_pos.le⟩ ⟨hu, hup⟩ hu
    have hqle' : Real.exp (lam * u) *
        (Real.cos u - lam * Real.sin u) ≤ 1 := by
      simpa [q] using hqle
    have hneg : -Real.exp (-lam * Real.pi) ≤
        (-Real.exp (-lam * Real.pi)) *
          (Real.exp (lam * u) *
            (Real.cos u - lam * Real.sin u)) := by
      have hmul := mul_le_mul_of_nonpos_left hqle'
        (neg_nonpos.mpr (Real.exp_pos (-lam * Real.pi)).le)
      simpa using hmul
    calc
      -Real.exp (-lam * Real.pi) ≤
          (-Real.exp (-lam * Real.pi)) *
            (Real.exp (lam * u) *
              (Real.cos u - lam * Real.sin u)) := hneg
      _ = Real.exp (-lam * t) * (Real.cos t + lam * Real.sin t) := by
        have ht_eq : t = Real.pi - u := by exact Eq.symm (sub_sub_self Real.pi t)
        rw [ht_eq]
        rw [show -lam * (Real.pi - u) = (-lam * Real.pi) + lam * u by ring,
          Real.exp_add]
        rw [show Real.pi - u = (-u) + Real.pi by ring,
          Real.cos_add_pi, Real.sin_add_pi]
        simp [Real.cos_neg, Real.sin_neg]
        ring
  · have hpi : Real.pi ≤ t := le_of_not_ge htp
    let u : ℝ := t - Real.pi
    have hu : 0 ≤ u := sub_nonneg.mpr hpi
    have hsin : Real.sin u ≤ u := Real.sin_le hu
    have hcos : Real.cos u ≤ 1 := Real.cos_le_one _
    have hlin : Real.cos u + lam * Real.sin u ≤ 1 + lam * u := by
      nlinarith
    have hexp : 1 + lam * u ≤ Real.exp (lam * u) := by
      simpa [add_comm] using (Real.add_one_le_exp (lam * u))
    have hq : Real.exp (-lam * u) * (Real.cos u + lam * Real.sin u) ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left (hlin.trans hexp)
        (Real.exp_pos (-lam * u)).le
      calc
        Real.exp (-lam * u) * (Real.cos u + lam * Real.sin u)
            ≤ Real.exp (-lam * u) * Real.exp (lam * u) := hmul
        _ = 1 := by
          rw [← Real.exp_add]
          simp
    have hneg : -Real.exp (-lam * Real.pi) ≤
        (-Real.exp (-lam * Real.pi)) *
          (Real.exp (-lam * u) * (Real.cos u + lam * Real.sin u)) := by
      have hmul := mul_le_mul_of_nonpos_left hq
        (neg_nonpos.mpr (Real.exp_pos (-lam * Real.pi)).le)
      simpa using hmul
    calc
      -Real.exp (-lam * Real.pi) ≤
          (-Real.exp (-lam * Real.pi)) *
            (Real.exp (-lam * u) * (Real.cos u + lam * Real.sin u)) := hneg
      _ = Real.exp (-lam * t) * (Real.cos t + lam * Real.sin t) := by
        have ht_eq : t = u + Real.pi := by
          exact Eq.symm (sub_add_cancel t Real.pi)
        rw [ht_eq, Real.cos_add_pi, Real.sin_add_pi]
        rw [show -lam * (u + Real.pi) = (-lam * u) + (-lam * Real.pi) by ring,
          Real.exp_add]
        ring

private lemma term_re (r θ lam : ℝ) (k : ℕ) :
    (((1 : ℂ) + (lam : ℂ) * Complex.I) *
      (((r : ℂ) * Complex.exp ((-θ) * Complex.I)) ^ k)).re =
      r ^ k * (Real.cos (k * θ) + lam * Real.sin (k * θ)) := by
  rw [mul_pow]
  rw [← Complex.exp_nat_mul]
  have hrpow : ((r : ℂ) ^ k) = ((r ^ k : ℝ) : ℂ) := by norm_cast
  rw [hrpow]
  rw [show (k : ℂ) * (-((θ : ℂ)) * Complex.I) = ((-(k * θ) : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub,
    one_mul, mul_one]
  rw [Real.cos_neg, Real.sin_neg]
  ring

private lemma escape_mass_bound {ι : Type*} [Fintype ι]
    (a f : ι → ℝ) (a0 E : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hf : ∀ i, -E ≤ f i)
    (heq : a0 + ∑ i, a i * f i = 0) :
    a0 ≤ E * ∑ i, a i := by
  have hsum : -E * ∑ i, a i ≤ ∑ i, a i * f i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left (hf i) (ha i))
  nlinarith

private lemma escape_exponent_bound {r θ lam a0 A : ℝ}
    (hθ : 0 < θ)
    (hrrep : r = Real.exp (lam * θ)) (ha0 : 0 < a0)
    (hmass : a0 ≤ Real.exp (-lam * Real.pi) * A) :
    r ≤ (A / a0) ^ (θ / Real.pi) := by
  have hA : Real.exp (lam * Real.pi) ≤ A / a0 := by
    apply (le_div_iff₀ ha0).2
    calc
      Real.exp (lam * Real.pi) * a0 ≤
          Real.exp (lam * Real.pi) *
            (Real.exp (-lam * Real.pi) * A) :=
        mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
      _ = A := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
  have hp : 0 ≤ θ / Real.pi := div_nonneg hθ.le Real.pi_pos.le
  have hpow := Real.rpow_le_rpow (Real.exp_pos _).le hA hp
  calc
    r = Real.exp (lam * θ) := hrrep
    _ = Real.exp ((lam * Real.pi) * (θ / Real.pi)) := by
      congr 1
      field_simp [Real.pi_ne_zero]
    _ = Real.exp (lam * Real.pi) ^ (θ / Real.pi) := Real.exp_mul _ _
    _ ≤ (A / a0) ^ (θ / Real.pi) := hpow

private lemma inverse_polar (z : ℂ) :
    z⁻¹ = ((‖z‖⁻¹ : ℝ) : ℂ) * Complex.exp ((-z.arg) * Complex.I) := by
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_inv_rev, ← Complex.exp_neg]
  norm_num [Complex.ofReal_inv]
  ring

private lemma inverse_power_re {z : ℂ} {lam : ℝ}
    (hrrep : ‖z‖ = Real.exp (lam * z.arg)) (k : ℕ) :
    (((1 : ℂ) + (lam : ℂ) * Complex.I) * (z⁻¹ ^ k)).re =
      Real.exp (-lam * ((k : ℝ) * z.arg)) *
        (Real.cos ((k : ℝ) * z.arg) + lam * Real.sin ((k : ℝ) * z.arg)) := by
  rw [inverse_polar, term_re]
  have hpow : (‖z‖⁻¹ : ℝ) ^ k = Real.exp (-lam * ((k : ℝ) * z.arg)) := by
    rw [hrrep, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow]

private lemma normalized_escape_bound_pos {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → ℕ) (a0 : ℝ) (z : ℂ)
    (ha : ∀ i, 0 ≤ a i) (ha0 : 0 < a0)
    (hnorm : 1 < ‖z‖) (harg : 0 < z.arg)
    (hroot : (a0 : ℂ) + ∑ i, (a i : ℂ) * (z⁻¹ ^ k i) = 0) :
    ‖z‖ ≤ ((∑ i, a i) / a0) ^ (z.arg / Real.pi) := by
  let lam := Real.log ‖z‖ / z.arg
  have hlam : 0 < lam := div_pos (Real.log_pos hnorm) harg
  have hrrep : ‖z‖ = Real.exp (lam * z.arg) := by
    dsimp [lam]
    rw [div_mul_cancel₀ _ (ne_of_gt harg), Real.exp_log (lt_trans zero_lt_one hnorm)]
  let R : ℂ := (1 : ℂ) + (lam : ℂ) * Complex.I
  let f : ι → ℝ := fun i => (R * (z⁻¹ ^ k i)).re
  have heq : a0 + ∑ i, a i * f i = 0 := by
    have hm := congrArg (fun w : ℂ => (R * w).re) hroot
    rw [mul_add, Finset.mul_sum, Complex.add_re, Complex.re_sum] at hm
    have hlead : (R * (a0 : ℂ)).re = a0 := by
      simp [R, Complex.mul_re, Complex.mul_im]
    have hw (i : ι) : (R * ((a i : ℂ) * (z⁻¹ ^ k i))).re = a i * f i := by
      dsimp [f]
      rw [← mul_assoc, mul_comm R (a i : ℂ), mul_assoc]
      simp [Complex.mul_re]
    simp_rw [hlead, hw] at hm
    simpa only [mul_zero, Complex.zero_re] using hm
  have hf (i : ι) : -Real.exp (-lam * Real.pi) ≤ f i := by
    dsimp [f, R]
    rw [inverse_power_re hrrep]
    exact damped_trig_bound hlam (mul_nonneg (Nat.cast_nonneg _) harg.le)
  have hmass := escape_mass_bound a f a0 (Real.exp (-lam * Real.pi)) ha hf heq
  exact escape_exponent_bound harg hrrep ha0 hmass

private lemma normalized_root_arg_ne_zero {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → ℕ) (a0 : ℝ) (z : ℂ)
    (ha : ∀ i, 0 ≤ a i) (ha0 : 0 < a0)
    (hroot : (a0 : ℂ) + ∑ i, (a i : ℂ) * (z⁻¹ ^ k i) = 0) : z.arg ≠ 0 := by
  intro harg
  have hzre : 0 ≤ z.re := (Complex.arg_eq_zero_iff.mp harg).1
  have hzim : z.im = 0 := (Complex.arg_eq_zero_iff.mp harg).2
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext_iff.mpr
    simp [hzim]
  have hzinv : z⁻¹ = ((z.re⁻¹ : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_inv] using congrArg (fun w : ℂ => w⁻¹) hzreal
  have heq : a0 + ∑ i, a i * (z.re⁻¹ ^ k i) = 0 := by
    have he := congrArg Complex.re hroot
    rw [hzinv] at he
    simpa only [Complex.add_re, Complex.re_sum, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.zero_re] using he
  have hs : 0 ≤ ∑ i, a i * (z.re⁻¹ ^ k i) := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i)
      (pow_nonneg (inv_nonneg.mpr hzre) _))
  linarith

lemma normalized_escape_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → ℕ) (a0 : ℝ) (z : ℂ)
    (ha : ∀ i, 0 ≤ a i) (ha0 : 0 < a0) (hnorm : 1 < ‖z‖)
    (hroot : (a0 : ℂ) + ∑ i, (a i : ℂ) * (z⁻¹ ^ k i) = 0) :
    ‖z‖ ≤ ((∑ i, a i) / a0) ^ (|z.arg| / Real.pi) := by
  by_cases harg : 0 < z.arg
  · simpa only [abs_of_pos harg] using
      normalized_escape_bound_pos a k a0 z ha ha0 hnorm harg hroot
  · have hargne := normalized_root_arg_ne_zero a k a0 z ha ha0 hroot
    have hneg : z.arg < 0 := lt_of_le_of_ne (le_of_not_gt harg) hargne
    have hpi : z.arg ≠ Real.pi := by linarith [Real.pi_pos]
    have hrootc : (a0 : ℂ) + ∑ i, (a i : ℂ) * ((starRingEnd ℂ z)⁻¹ ^ k i) = 0 := by
      simpa using congrArg (starRingEnd ℂ) hroot
    have hnormc : 1 < ‖starRingEnd ℂ z‖ := by simpa using hnorm
    have hargc : 0 < (starRingEnd ℂ z).arg := by
      rw [Complex.arg_conj, if_neg hpi]
      linarith
    have hb := normalized_escape_bound_pos a k a0 (starRingEnd ℂ z)
      ha ha0 hnormc hargc hrootc
    simpa only [Complex.norm_conj, Complex.arg_conj, if_neg hpi, abs_of_neg hneg] using hb

end D5.S3.Zeros.DegreeRoots.EscapeWitness
