/- GID: D5/S3/Weil/Analytic/NymanFixedRationalKernelMellin
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanFixedRationalKernelMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact nonvanishing Mellin transform of the fixed rational kernel. -/

import D5.S3.Weil.Analytic.NymanFixedRationalKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.MellinTransform
import OmegaBuild.Commands

/-! Exact nonvanishing Mellin transform of the fixed rational kernel. -/

compile_only_with_mathlib

set_option autoImplicit false

open Complex Set MeasureTheory intervalIntegral Finset
open scoped BigOperators

namespace NymanFixedRationalKernel

noncomputable section

private def primitive (a : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  (a:ℂ)⁻¹^3 * (x:ℂ)^(s+3)/(s+3) -
  3*(a:ℂ)⁻¹^2 * (x:ℂ)^(s+2)/(s+2) +
  3*(a:ℂ)⁻¹ * (x:ℂ)^(s+1)/(s+1) - (x:ℂ)^s/s

private theorem primitive_coeffs (a x : ℝ) (hx : 0<x) (s : ℂ) :
    (x:ℂ)^(s-1)*((x:ℂ)/(a:ℂ)-1)^3 =
      (a:ℂ)⁻¹^3*(x:ℂ)^(s+3-1) -
      3*(a:ℂ)⁻¹^2*(x:ℂ)^(s+2-1) +
      3*(a:ℂ)⁻¹*(x:ℂ)^(s+1-1) - (x:ℂ)^(s-1) := by
  have hx0 : (x:ℂ)≠0 := ofReal_ne_zero.mpr hx.ne'
  have h3 : (x:ℂ)^(s+3-1)=(x:ℂ)^(s-1)*(x:ℂ)^3 := by
    rw [show s+3-1=s-1+3 by ring,cpow_add _ _ hx0]
    simp
  have h2 : (x:ℂ)^(s+2-1)=(x:ℂ)^(s-1)*(x:ℂ)^2 := by
    rw [show s+2-1=s-1+2 by ring,cpow_add _ _ hx0]
    simp
  have h1 : (x:ℂ)^(s+1-1)=(x:ℂ)^(s-1)*(x:ℂ) := by
    rw [show s+1-1=s-1+1 by ring,cpow_add _ _ hx0,cpow_one]
  rw [h3,h2,h1,div_eq_mul_inv]
  ring

private theorem primitive_integral {s : ℂ} (hs : 0<s.re) {a : ℝ}
    (ha : 1≤a) (ha2 : a≤2) :
    (∫ x : ℝ in a..2, (x:ℂ)^(s-1)*((x:ℂ)/(a:ℂ)-1)^3) =
      primitive a s 2-primitive a s a := by
  have hpos : ∀ x∈Ioo a (2:ℝ), 0<x := fun x hx => by linarith [hx.1]
  have hI (j : ℕ) : IntervalIntegrable (fun x : ℝ => (x:ℂ)^(s+(j:ℂ)-1)) volume a 2 := by
    apply intervalIntegrable_cpow'
    simp
    have : 0≤(j:ℝ) := by positivity
    linarith
  have h0 : IntervalIntegrable (fun x : ℝ => (x:ℂ)^(s-1)) volume a 2 := by
    simpa using hI 0
  have h1 : IntervalIntegrable (fun x : ℝ => (3*(a:ℂ)⁻¹)*(x:ℂ)^(s+1-1)) volume a 2 := by simpa using (hI 1).const_mul (3*(a:ℂ)⁻¹)
  have h2 : IntervalIntegrable (fun x : ℝ => (3*(a:ℂ)⁻¹^2)*(x:ℂ)^(s+2-1)) volume a 2 := by simpa only [Nat.cast_ofNat] using (hI 2).const_mul (3*(a:ℂ)⁻¹^2)
  have h3 : IntervalIntegrable (fun x : ℝ => (a:ℂ)⁻¹^3*(x:ℂ)^(s+3-1)) volume a 2 := by simpa only [Nat.cast_ofNat] using (hI 3).const_mul ((a:ℂ)⁻¹^3)
  calc
    _ = ∫ x : ℝ in a..2,
      (a:ℂ)⁻¹^3*(x:ℂ)^(s+3-1) - 3*(a:ℂ)⁻¹^2*(x:ℂ)^(s+2-1) +
      3*(a:ℂ)⁻¹*(x:ℂ)^(s+1-1) - (x:ℂ)^(s-1) :=
        intervalIntegral.integral_congr_Ioo_of_le ha2 (fun x hx => primitive_coeffs a x (hpos x hx) s)
    _ = _ := by
      rw [intervalIntegral.integral_sub ((h3.sub h2).add h1) h0,
        intervalIntegral.integral_add (h3.sub h2) h1,intervalIntegral.integral_sub h3 h2]
      simp only [intervalIntegral.integral_const_mul]
      rw [integral_cpow (r:=s+3-1) (Or.inl (by simp; linarith)),
        integral_cpow (r:=s+2-1) (Or.inl (by simp; linarith)),
        integral_cpow (r:=s+1-1) (Or.inl (by simp; linarith)),
        integral_cpow (r:=s-1) (Or.inl (by simp; linarith))]
      simp [primitive]
      ring

private theorem cut_integral {s : ℂ} (hs : 0<s.re) {a : ℝ}
    (ha : 1≤a) (ha2 : a≤2) :
    (∫ x : ℝ in 1..2, (x:ℂ)^(s-1)*((max (x/a-1) 0 : ℝ):ℂ)^3) =
      primitive a s 2-primitive a s a := by
  have hcont : ContinuousOn (fun x : ℝ => (x:ℂ)^(s-1)*((max (x/a-1) 0 : ℝ):ℂ)^3)
      (Icc (1:ℝ) 2) := by
    apply ContinuousOn.mul
    · intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x (s-1) (Or.inr (by have := hx.1; linarith))).continuousWithinAt
    · fun_prop
  have hI : IntervalIntegrable (fun x : ℝ => (x:ℂ)^(s-1)*((max (x/a-1) 0 : ℝ):ℂ)^3)
      volume 1 2 := hcont.intervalIntegrable_of_Icc (by norm_num)
  have hIa := hI.mono_set (show Set.uIcc (1:ℝ) a ⊆ Set.uIcc (1:ℝ) 2 by rw [uIcc_of_le ha,uIcc_of_le (by norm_num : (1:ℝ)≤2)]; exact Icc_subset_Icc_right ha2)
  have hIb := hI.mono_set (show Set.uIcc a (2:ℝ) ⊆ Set.uIcc (1:ℝ) 2 by rw [uIcc_of_le ha2,uIcc_of_le (by norm_num : (1:ℝ)≤2)]; exact Icc_subset_Icc_left ha)
  rw [← intervalIntegral.integral_add_adjacent_intervals hIa hIb]
  have hz : (∫ x : ℝ in 1..a, (x:ℂ)^(s-1)*((max (x/a-1) 0 : ℝ):ℂ)^3)=0 := by
    calc
      _ = ∫ x : ℝ in 1..a, (0:ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha
        intro x hx
        dsimp only
        rw [max_eq_right (sub_nonpos.mpr ((div_le_iff₀ (by linarith)).mpr (by simpa using hx.2.le)))]
        simp
      _ = 0 := by simp
  rw [hz,zero_add,← primitive_integral hs ha ha2]
  apply intervalIntegral.integral_congr_Ioo_of_le ha2
  intro x hx
  dsimp only
  rw [max_eq_left (sub_nonneg.mpr ((le_div_iff₀ (by linarith)).mpr (by simpa using hx.1.le)))]
  push_cast
  rfl

private theorem primitive_at_left {s : ℂ} (hs : 0<s.re) {a : ℝ} (ha : 0<a) :
    primitive a s a = -6*(a:ℂ)^s/(s*(s+1)*(s+2)*(s+3)) := by
  have ha0 : (a:ℂ)≠0 := ofReal_ne_zero.mpr ha.ne'
  have h0 : s≠0 := by intro h; rw [h,zero_re] at hs; linarith
  have h1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : s+2≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : s+3≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold primitive
  rw [cpow_add _ _ ha0,cpow_add _ _ ha0,cpow_add _ _ ha0]
  simp only [cpow_one,cpow_ofNat]
  field_simp [ha0,h0,h1,h2,h3]
  ring

private theorem primitive_top_cancel (s : ℂ) :
    ∑ j : Fin 5, (c j:ℂ)*primitive (A^j.val) s 2 = 0 := by
  norm_num [Fin.sum_univ_succ,c,A,primitive]
  ring

private theorem cpow_of_power (s : ℂ) (j : ℕ) :
    ((A^j:ℝ):ℂ)^s=((A:ℂ)^s)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ,ofReal_mul,mul_cpow_ofReal_nonneg (pow_nonneg A_pos.le _) A_pos.le,ih,pow_succ]

/-- Explicit Mellin integral on the compact support. Its four factors are all
nonzero in the right half-plane. -/
private theorem interval_mellin_formula {s : ℂ} (hs : 0<s.re) :
    (∫ x : ℝ in 1..2, (x:ℂ)^(s-1)*(b x:ℂ)) =
      ((A:ℂ)^s-1)*((A:ℂ)^(s+1)-1)*((A:ℂ)^(s+2)-1)*((A:ℂ)^(s+3)-1)/(s*(s+1)*(s+2)*(s+3)) := by
  let den := s*(s+1)*(s+2)*(s+3)
  have hcut (j : Fin 5) : 1≤A^j.val ∧ A^j.val≤2 :=
    ⟨one_le_pow₀ one_lt_A.le,(pow_le_pow_right₀ one_lt_A.le (by omega : j.val≤4)).trans A4_lt_two.le⟩
  have hI (j : Fin 5) : IntervalIntegrable (fun x : ℝ => (c j:ℂ)*((x:ℂ)^(s-1)*((max (x/A^j.val-1) 0 : ℝ):ℂ)^3)) volume 1 2 := by
    apply IntervalIntegrable.const_mul
    have hcont : ContinuousOn (fun x : ℝ => (x:ℂ)^(s-1)*((max (x/A^j.val-1) 0 : ℝ):ℂ)^3) (Icc (1:ℝ) 2) := by
      apply ContinuousOn.mul
      · intro x hx
        exact (Complex.continuousAt_ofReal_cpow_const x (s-1) (Or.inr (by have := hx.1; linarith))).continuousWithinAt
      · fun_prop
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hEq : (∫ x : ℝ in 1..2, (x:ℂ)^(s-1)*(b x:ℂ)) =
      (∑ j : Fin 5, (c j:ℂ)*(primitive (A^j.val) s 2-primitive (A^j.val) s (A^j.val)))/6 := by
    calc
      _ = (∫ x : ℝ in 1..2, ∑ j : Fin 5, (c j:ℂ)*((x:ℂ)^(s-1)*((max (x/A^j.val-1) 0 : ℝ):ℂ)^3))/6 := by
        rw [← intervalIntegral.integral_div]
        apply intervalIntegral.integral_congr
        intro x hx
        unfold b
        push_cast
        rw [← mul_div_assoc,mul_sum]
        congr 1
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum (fun j _ => hI j)]
        congr 1
        apply sum_congr rfl
        intro j _
        rw [intervalIntegral.integral_const_mul,cut_integral hs (hcut j).1 (hcut j).2]
  rw [hEq]
  simp_rw [mul_sub]
  rw [sum_sub_distrib,primitive_top_cancel,zero_sub]
  simp_rw [primitive_at_left hs (pow_pos A_pos _)]
  change -(∑ j : Fin 5, (c j:ℂ)*(-6*((A^j.val:ℝ):ℂ)^s/den))/6 = _
  have hsum : (∑ j : Fin 5, (c j:ℂ)*(-6*((A^j.val:ℝ):ℂ)^s/den)) =
      -6*(∑ j : Fin 5, (c j:ℂ)*((A:ℂ)^s)^j.val)/den := by
    rw [mul_sum,sum_div]
    apply sum_congr rfl
    intro j _
    rw [cpow_of_power]
    ring
  rw [hsum,coefficient_product]
  have hA0 : (A:ℂ)≠0 := ofReal_ne_zero.mpr A_pos.ne'
  rw [cpow_add _ _ hA0,cpow_add _ _ hA0,cpow_add _ _ hA0]
  simp only [cpow_one,cpow_ofNat]
  unfold den
  ring

/-- Exact Mellin transform of the fixed rational compactly supported kernel. -/
theorem mellin_formula {s : ℂ} (hs : 0<s.re) :
    mellin (fun u : ℝ => (b u:ℂ)) s =
      ((A:ℂ)^s-1)*((A:ℂ)^(s+1)-1)*((A:ℂ)^(s+2)-1)*((A:ℂ)^(s+3)-1)/(s*(s+1)*(s+2)*(s+3)) := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s:=Ioc (1:ℝ) 2) measurableSet_Ioi (by intro x hx; exact (by linarith [hx.1] : 0<x))]
  · rw [← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]
    exact interval_mellin_formula hs
  · intro x hx
    rw [b_zero_off x (fun h => hx.2 ⟨h.1,h.2.le⟩),ofReal_zero,mul_zero]

private theorem cpow_sub_one_ne_zero {z : ℂ} (hz : 0<z.re) : (A:ℂ)^z-1≠0 := by
  have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos A_pos z
  intro h
  have he := sub_eq_zero.mp h
  rw [he,norm_one] at hnorm
  exact (ne_of_gt (Real.one_lt_rpow one_lt_A hz)) hnorm.symm

/-- The Mellin transform of the fixed rational shell kernel is nonzero for Re(s) > 0. -/
theorem mellin_ne_zero {s : ℂ} (hs : 0<s.re) :
    mellin (fun u : ℝ => (b u:ℂ)) s ≠ 0 := by
  rw [mellin_formula hs]
  have h0 : s≠0 := by intro h; rw [h,zero_re] at hs; linarith
  have h1 : s+1≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : s+2≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : s+3≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (cpow_sub_one_ne_zero hs)
    (cpow_sub_one_ne_zero (by simp;linarith))) (cpow_sub_one_ne_zero (by simp;linarith)))
    (cpow_sub_one_ne_zero (by simp;linarith))) (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3)

end
end NymanFixedRationalKernel
