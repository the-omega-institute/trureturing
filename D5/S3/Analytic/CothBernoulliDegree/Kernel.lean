/- GID: D5/S3/Analytic/CothBernoulliDegree/Kernel
   generality: G
   mirror-B: D5/B/S3/Analytic/CothBernoulliDegree/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Pi.Bounds, mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv, mathlib/module/Mathlib.Topology.Algebra.InfiniteSum.Real, mathlib/module/Mathlib.Tactic, mathlib/module/Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas, mathlib/module/Mathlib.Analysis.Calculus.Deriv.ZPow, mathlib/module/Mathlib.Analysis.Complex.RealDeriv]
   utility: none
   digest: Rational kernel derivative certificates and uniform phase and series estimates. -/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Tactic

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RealDeriv

namespace D5.S3.Analytic.CothBernoulliDegree.Kernel

open Set Real
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open Filter Complex

private lemma complex_certificate (N : ℕ) (c : ℂ) (z : ℝ) (hz : (z : ℂ) + c ≠ 0) :
    iteratedDeriv N (fun w : ℝ => (w : ℂ)^(N+1)/((w : ℂ)+c)) z =
      (N.factorial : ℂ) * (1 - (c/((z : ℂ)+c))^(N+1)) := by
  induction N generalizing z with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.zero_add, Nat.factorial_zero, Nat.cast_one, one_mul, pow_one]
    change (z : ℂ)/((z : ℂ)+c) = 1-c/((z : ℂ)+c)
    rw [show (1 : ℂ) = ((z : ℂ)+c)/((z : ℂ)+c) from (div_self hz).symm, ← sub_div]
    congr 1
    ring
  | succ N ih =>
    have hlocal : ∀ᶠ w : ℝ in 𝓝 z, (w : ℂ)+c ≠ 0 :=
      (Complex.continuous_ofReal.continuousAt.add continuousAt_const).eventually (eventually_ne_nhds hz)
    have he : (fun w : ℝ => (w : ℂ)^(N+1+1)/((w : ℂ)+c)) =ᶠ[𝓝 z]
        (fun w : ℝ => (w : ℂ)^(N+1) - c*((w : ℂ)^(N+1)/((w : ℂ)+c))) := by
      filter_upwards [hlocal] with w hw
      field_simp [hz, hw] <;>
      ring
    have hg : ContDiffAt ℝ (N+1) (fun w : ℝ => (w : ℂ)^(N+1)/((w : ℂ)+c)) z := by
      have ho : ContDiffAt ℝ (N+1) (fun w : ℝ => (w : ℂ)) z :=
        Complex.ofRealCLM.contDiff.contDiffAt
      simpa only [div_eq_mul_inv] using!
        (ho.pow (N+1)).mul ((ho.add contDiffAt_const).inv hz)
    have hd : HasDerivAt (fun w : ℝ =>
        (N.factorial : ℂ) * (1-(c/((w : ℂ)+c))^(N+1)))
        ((N.factorial : ℂ) * ((N+1)*c^(N+1)/((z : ℂ)+c)^(N+2))) z := by
      convert (((hasDerivAt_const z c).div (Complex.ofRealCLM.hasDerivAt.add_const c) hz).pow
        (N+1)).const_sub 1 |>.const_mul (N.factorial : ℂ) using 1 <;>
        simp only [Pi.pow_apply, Pi.div_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
          mul_one, zero_mul, sub_zero, zero_sub] <;>
        simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one, div_pow] <;>
        field_simp [hz] <;> ring
    have he' : iteratedDeriv N (fun w : ℝ => (w : ℂ)^(N+1)/((w : ℂ)+c)) =ᶠ[𝓝 z]
        (fun w => (N.factorial : ℂ)*(1-(c/((w : ℂ)+c))^(N+1))) := by
      filter_upwards [hlocal] with w hw
      exact ih w hw
    rw [he.iteratedDeriv_eq (N+1), iteratedDeriv_fun_sub (show ContDiffAt ℝ (N+1) (fun w : ℝ => (w : ℂ)^(N+1)) z from Complex.ofRealCLM.contDiff.contDiffAt.pow (N+1)) (contDiffAt_const.mul hg),
      iteratedDeriv_const_mul_field]
    have hp : iteratedDeriv (N+1) (fun w : ℝ => (w : ℂ)^(N+1)) z = (N+1).factorial := by
      have h := Complex.ofRealCLM.iteratedFDeriv_comp_left
        (f := fun w : ℝ => w^(N+1)) (x := z) (n := (N+1 : ℕ)) (by fun_prop)
        (i := N+1) le_rfl
      have h' := congrArg (fun q => q (fun _ => (1 : ℝ))) h
      simp only [Complex.ofRealCLM_apply, Function.comp_def] at h'
      change iteratedDeriv (N+1) (fun w : ℝ => ((w^(N+1) : ℝ) : ℂ)) z =
        ((iteratedDeriv (N+1) (fun w : ℝ => w^(N+1)) z : ℝ) : ℂ) at h'
      simpa only [Complex.ofReal_pow, iteratedDeriv_pow, Nat.sub_self, pow_zero,
        Nat.descFactorial_self, mul_one] using! h'
    rw [hp, iteratedDeriv_succ, he'.deriv_eq, hd.deriv]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [div_pow]
    field_simp [hz] <;> ring

private lemma denominator_ne (a t : ℝ) (ha : 0 < a) :
    (t : ℂ) + -(a : ℂ)*I ≠ 0 := by
  intro h
  have h' := congrArg Complex.im h
  simp at h'
  linarith

private lemma real_part_kernel (N : ℕ) (a t : ℝ) :
    (((t : ℂ)^(N+1)/((t : ℂ)+ -(a : ℂ)*I)).re) =
      t^(N+2)/(t^2+a^2) := by
  simp only [← Complex.ofReal_pow, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
  simp only [mul_zero, mul_one, zero_mul, neg_zero, add_zero, zero_add, zero_sub, sub_zero]
  simp only [pow_succ]
  ring

lemma kernel_deriv_N (N : ℕ) (a t : ℝ) (ha : 0 < a) :
    iteratedDeriv N (fun s : ℝ => s^(N+2)/(s^2+a^2)) t =
      (N.factorial : ℝ) * (1 - ((1 + I*(t:ℂ)/(a:ℂ))^(-((N+1 : ℕ) : ℤ))).re) := by
  have hz := denominator_ne a t ha
  let f : ℝ → ℂ := fun s => (s : ℂ)^(N+1)/((s : ℂ)+ -(a : ℂ)*I)
  have hf : ContDiffAt ℝ N f t := by
    dsimp [f]
    have ho : ContDiffAt ℝ N (fun w : ℝ => (w : ℂ)) t :=
      Complex.ofRealCLM.contDiff.contDiffAt
    simpa only [div_eq_mul_inv] using!
      (ho.pow (N+1)).mul ((ho.add contDiffAt_const).inv hz)
  have h := Complex.reCLM.iteratedFDeriv_comp_left hf (i := N) le_rfl
  have he := congrArg (fun q => q (fun _ => (1 : ℝ))) h
  change iteratedDeriv N (fun s => (f s).re) t = (iteratedDeriv N f t).re at he
  have hfn : (fun s => (f s).re) = (fun s : ℝ => s^(N+2)/(s^2+a^2)) := by
    ext s
    exact real_part_kernel N a s
  rw [hfn] at he
  rw [he, show iteratedDeriv N f t = _ from complex_certificate N (-(a : ℂ)*I) t hz]
  have hratio : (-(a:ℂ)*I)/((t:ℂ)+ -(a:ℂ)*I) = (1+I*(t:ℂ)/(a:ℂ))⁻¹ := by
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hc : -(a : ℂ)*I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr ha') I_ne_zero
    have hden : (t : ℂ)+ -(a : ℂ)*I = (-(a : ℂ)*I)*(1+I*(t : ℂ)/(a : ℂ)) := by
      field_simp [ha']
      ring_nf
      simp only [I_sq]
      ring
    rw [hden, ← div_div, div_self hc, one_div]
  rw [hratio]
  rw [zpow_neg, zpow_natCast, inv_pow]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.sub_re,
    Complex.one_re, zero_mul, sub_zero]


lemma kernel_deriv_N_pos (N : ℕ) (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    0 < iteratedDeriv N (fun s : ℝ => s^(N+2)/(s^2+a^2)) t := by
  rw [kernel_deriv_N N a t ha]
  apply mul_pos (by positivity)
  apply sub_pos.mpr
  apply lt_of_le_of_lt (Complex.re_le_norm _)
  have hnorm : 1 < ‖(1 : ℂ) + I*(t:ℂ)/(a:ℂ)‖ := by
    have hsq : ‖(1 : ℂ) + I*(t:ℂ)/(a:ℂ)‖^2 = 1+(t/a)^2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq, Complex.div_re, Complex.div_im]
      field_simp
      <;> ring
    have hta : 0 < t/a := div_pos ht ha
    nlinarith [norm_nonneg ((1 : ℂ) + I*(t:ℂ)/(a:ℂ)), sq_pos_of_pos hta]
  simp only [zpow_neg, zpow_natCast, norm_inv, norm_pow]
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hnorm (by omega))

private lemma kernel_deriv_succ_im (N : ℕ) (a t : ℝ) (ha : 0 < a) :
    iteratedDeriv (N+1) (fun s : ℝ => s^(N+2)/(s^2+a^2)) t =
      (N+1).factorial / a * -((1+I*(t:ℂ)/(a:ℂ))^(-((N+2:ℕ):ℤ))).im := by
  let b : ℝ → ℂ := fun s => 1+I*(s:ℂ)/(a:ℂ)
  have hb : HasDerivAt b (I/(a:ℂ)) t := by
    convert ((Complex.ofRealCLM.hasDerivAt.const_mul I).div_const (a:ℂ)).const_add 1 using 1 <;>
      simp [b]
  have hb0 : b t ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp [b, Complex.div_re] at h
  have hz := (hasDerivAt_zpow (-((N+1:ℕ):ℤ)) (b t) (Or.inl hb0)).hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt t hb
  have hz' : HasDerivAt (fun s => b s ^ (-((N+1:ℕ):ℤ)))
      (((-((N+1:ℕ):ℂ)) * b t ^ (-((N+1:ℕ):ℤ)-1)) * (I/(a:ℂ))) t := by
    simpa only [Complex.restrictScalars_toSpanSingleton, smul_apply,
      one_apply_eq_self, smul_eq_mul, Function.comp_def, Int.cast_neg, Int.cast_natCast] using! hz
  have hr : HasDerivAt (fun s => (b s ^ (-((N+1:ℕ):ℤ))).re)
      (((-((N+1:ℕ):ℂ)) * b t ^ (-((N+1:ℕ):ℤ)-1)) * (I/(a:ℂ))).re t := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz'
  have hh := (hr.const_sub 1).const_mul (N.factorial:ℝ)
  rw [iteratedDeriv_succ, show iteratedDeriv N (fun s : ℝ => s^(N+2)/(s^2+a^2)) =
      (fun s => (N.factorial:ℝ)*(1-(b s^(-((N+1:ℕ):ℤ))).re)) from
      funext (fun s => kernel_deriv_N N a s ha)]
  rw [hh.deriv]
  have he : -((N+1:ℕ):ℤ)-1 = -((N+2:ℕ):ℤ) := by omega
  simp only [he, Complex.reCLM_apply, Int.cast_neg, Int.cast_natCast,
    neg_mul, Complex.mul_re, Complex.neg_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_re, Complex.div_im,
    Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.normSq_ofReal, zero_mul, mul_zero, zero_div,
    sub_zero, zero_sub, one_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  dsimp [b]
  field_simp [ha.ne']
  <;> ring


private lemma polar_neg_im (x : ℝ) (q : ℕ) :
    -((1 + Complex.I * (x : ℂ)) ^ (-(q : ℤ))).im =
      (1 + x ^ 2 : ℝ) ^ (-(q : ℝ) / 2) *
        Real.sin ((q : ℝ) * Real.arctan x) := by
  let z : ℂ := 1 + Complex.I * (x : ℂ)
  have hnorm : ‖z‖ = Real.sqrt (1 + x ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp [z]
  have harg : Complex.arg z = Real.arctan x := by
    rw [Complex.arg_of_re_nonneg (by simp [z]), hnorm]
    simp [z, Real.arctan_eq_arcsin]
  have hpow : z ^ (-(q : ℤ)) = z ^ ((-(q : ℝ)) : ℂ) := by
    rw [← Complex.cpow_intCast]
    simp only [Int.cast_neg, Int.cast_natCast, Complex.ofReal_natCast]
  change -(z ^ (-(q : ℤ))).im = _
  rw [hpow, ← Complex.ofReal_neg, Complex.cpow_ofReal_im, hnorm, harg,
    ← Real.rpow_div_two_eq_sqrt (-(q : ℝ)) (by positivity),
    mul_neg, Real.sin_neg, mul_comm (Real.arctan x) (q : ℝ)]
  ring


lemma kernel_deriv_succ (N : ℕ) (a t : ℝ) (ha : 0 < a) :
    iteratedDeriv (N+1) (fun s : ℝ => s^(N+2)/(s^2+a^2)) t =
      (N+1).factorial / a * (1+(t/a)^2 : ℝ)^(-((N+2:ℕ):ℝ)/2) *
        Real.sin (((N+2:ℕ):ℝ)*Real.arctan (t/a)) := by
  rw [kernel_deriv_succ_im N a t ha]
  have he : I*(t:ℂ)/(a:ℂ) = I*((t/a:ℝ):ℂ) := by
    push_cast
    ring
  rw [he, polar_neg_im (t/a) (N+2)]
  ring


private lemma arctan_chord (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : Real.pi / 4 * x ≤ Real.arctan x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) 1) Real.arctan := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1)
      Real.continuous_arctan.continuousOn
      Real.differentiable_arctan.differentiableOn
    intro a ha b hb hab
    rw [Real.deriv_arctan]
    apply one_div_le_one_div_of_le (by positivity)
    have ha0 : 0 ≤ a := (interior_subset ha).1
    nlinarith
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (sub_nonneg.mpr hx.2) hx.1 (by ring : (1-x)+x=1)
  simpa [Real.arctan_one, mul_comm] using h

private lemma log_sq_chord (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : Real.log (1+x^2) ≤ x * Real.log 2 := by
  have hd (a : ℝ) : HasDerivAt (fun y : ℝ => Real.log (1+y^2)) (2*a/(1+a^2)) a := by
    have hpow : HasDerivAt (fun y : ℝ => 1+y^2) (2*a) a := by
      convert ((hasDerivAt_id a).pow 2).const_add 1 using 1 <;> simp <;> ring
    convert hpow.log (by positivity) using 1 <;> ring
  have hc : ConvexOn ℝ (Icc (0:ℝ) 1) (fun y : ℝ => Real.log (1+y^2)) := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
      (fun a _ => (hd a).continuousAt.continuousWithinAt)
      (fun a _ => (hd a).differentiableAt.differentiableWithinAt)
    intro a ha b hb hab
    rw [(hd a).deriv, (hd b).deriv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have ha0 : 0 ≤ a := (interior_subset ha).1
    have hb1 : b ≤ 1 := (interior_subset hb).2
    have hb0 : 0 ≤ b := ha0.trans hab
    have ha1 : a ≤ 1 := hab.trans hb1
    have hprod : a*b ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hb0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hprod)]
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (sub_nonneg.mpr hx.2) hx.1 (by ring : (1-x)+x=1)
  norm_num at h
  simpa using h

private lemma phase_sin_bound (M : ℝ) (hM : 5 ≤ M) :
    Real.sin (M * Real.arctan (5/M)) ≤ - Real.sqrt 2 / 2 := by
  have hMp : 0 < M := by linarith
  have hx : (5/M : ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity, (div_le_one hMp).2 hM⟩
  have hlo := mul_le_mul_of_nonneg_left (arctan_chord (5/M) hx) hMp.le
  have hhi := mul_le_mul_of_nonneg_left (Real.arctan_le_self hx.1) hMp.le
  have heq : M * (Real.pi / 4 * (5/M)) = 5*Real.pi/4 := by field_simp
  have heq' : M * (5/M) = 5 := by field_simp
  rw [heq] at hlo
  rw [heq'] at hhi
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hd : |M * Real.arctan (5/M) - 3*Real.pi/2| ≤ Real.pi/4 := by
    rw [abs_le]; constructor <;> linarith
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (M * Real.arctan (5/M) - 3*Real.pi/2))
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) hd
  rw [Real.cos_abs, Real.cos_pi_div_four] at hc
  have htrig : Real.sin (M * Real.arctan (5/M)) =
      -Real.cos (M * Real.arctan (5/M) - 3*Real.pi/2) := by
    rw [show M * Real.arctan (5/M) - 3*Real.pi/2 =
      M * Real.arctan (5/M) - Real.pi/2 - Real.pi by ring,
      Real.cos_sub_pi, Real.cos_sub_pi_div_two]
    ring
  rw [htrig]
  linarith

private lemma amplitude_bound (M : ℝ) (hM : 5 ≤ M) :
    Real.sqrt 2 / 8 ≤ (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) := by
  have hMp : 0 < M := by linarith
  have hx : (5/M : ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity, (div_le_one hMp).2 hM⟩
  have hl := mul_le_mul_of_nonneg_left (log_sq_chord (5/M) hx) hMp.le
  have heq : M * ((5/M)* Real.log 2) = 5*Real.log 2 := by field_simp
  rw [heq] at hl
  have he : (2:ℝ)^(-(5:ℝ)/2) ≤ (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hv : (2:ℝ)^(-(5:ℝ)/2) = Real.sqrt 2 / 8 := by
    rw [show -(5:ℝ)/2 = 1/2-3 by norm_num, Real.rpow_sub (by norm_num)]
    rw [← Real.sqrt_eq_rpow]
    norm_num
  rwa [hv] at he

lemma phase_bound (M : ℝ) (hM : 5 ≤ M) :
    (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) * Real.sin (M*Real.arctan (5/M)) ≤ -(1:ℝ)/8 := by
  have ha := amplitude_bound M hM
  have hs := phase_sin_bound M hM
  have hp : 0 ≤ (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h := mul_le_mul_of_nonneg_left hs hp
  have h' := mul_le_mul_of_nonpos_right ha (show -Real.sqrt 2 / 2 ≤ 0 by have := Real.sqrt_nonneg (2:ℝ); linarith)
  have hsq : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

open scoped BigOperators

private lemma term_bound (k : ℕ) :
    1 / ((k : ℝ) + 2)^5 ≤
      (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : 0 < (k : ℝ) + 1 := by positivity
  have h2 : 0 < (k : ℝ) + 2 := by positivity
  have hs : 4 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2)^2 := by nlinarith [sq_nonneg (k : ℝ)]
  have hs' : 4 ≤ ((k : ℝ) + 2)^2 := by nlinarith
  have hp : 16 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2)^4 := by
    nlinarith [mul_le_mul hs hs' (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ ((k : ℝ) + 2)^2)]
  have heq :
      (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 =
        1 / (16 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp [ne_of_gt h1, ne_of_gt h2]
    ring
  rw [heq]
  apply one_div_le_one_div_of_le (by positivity)
  convert mul_le_mul_of_nonneg_right hp h2.le using 1; ring

lemma tail_bound (n : ℕ) (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / ((k : ℝ) + 2)^(2*n+1)) ≤ 1/16 := by
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro N
  have hterm (k : ℕ) :
      1 / ((k : ℝ) + 2)^(2*n+1) ≤
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 := by
    apply le_trans _ (term_bound k)
    apply one_div_le_one_div_of_le (by positivity : 0 < ((k : ℝ) + 2)^5)
    exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2) (by omega)
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = (1 - 1 / ((N : ℝ) + 1)) / 16 := by
      rw [← Finset.sum_div]
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_div_one,
        add_assoc, one_add_one_eq_two] using
        Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + 1)) N
    _ ≤ 1/16 := by
      have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith


end D5.S3.Analytic.CothBernoulliDegree.Kernel
