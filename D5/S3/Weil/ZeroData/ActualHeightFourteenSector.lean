/- GID: D5/S3/Weil/ZeroData/ActualHeightFourteenSector
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Generic polar-angle positivity, derivative monotonicity, and signed reduction for finite reciprocal products. -/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

open scoped BigOperators ComplexConjugate Topology

namespace H14Sector
open scoped BigOperators Topology
open Set Complex

def stripImaginary (u p : ℝ) : ℝ := Real.sqrt (u * (1 - 4 * p))

def factor {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) : ℂ :=
  ((u + p + c j : ℝ) : ℂ) + (stripImaginary u p : ℂ) * I

def reciprocalProduct {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℂ :=
  ∏ j, (factor c u p j)⁻¹

def weight {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℝ :=
  (reciprocalProduct c u p).re

private def angle {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) : ℝ :=
  Real.arctan (stripImaginary u p / (u + p + c j))

private def totalAngle {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℝ :=
  ∑ j, angle c u p j

private def amplitude {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) : ℝ :=
  ∏ j, ‖factor c u p j‖⁻¹

def threshold (N : ℕ) : ℝ := 4 * ((N : ℝ) + 1) ^ 2 / Real.pi ^ 2

private lemma factor_re {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) :
    (factor c u p j).re = u + p + c j := by simp [factor]

private lemma factor_im {N : ℕ} (c : Fin N → ℝ) (u p : ℝ) (j : Fin N) :
    (factor c u p j).im = stripImaginary u p := by simp [factor]

private lemma factor_real_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    0 < u + p + c j := by linarith [hc j]

private theorem factor_ne_zero {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    factor c u p j ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  have hx := factor_real_pos hc hu hp j
  simp only [factor_re, Complex.zero_re] at hr
  linarith

private lemma imaginary_bounds {u p : ℝ} (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) :
    0 ≤ stripImaginary u p ∧ stripImaginary u p ≤ Real.sqrt u := by
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt ?_⟩
  have h := mul_nonneg hu.le hp.1
  nlinarith

private lemma imaginary_sq {u p : ℝ} (hu : 0 < u) (hp : p ≤ 1 / 4) :
    stripImaginary u p ^ 2 = u * (1 - 4 * p) := by
  exact Real.sq_sqrt (mul_nonneg hu.le (by linarith))

private lemma imaginary_pos {u p : ℝ} (hu : 0 < u) (hp : p < 1 / 4) :
    0 < stripImaginary u p := by
  exact Real.sqrt_pos.2 (mul_pos hu (by linarith))

private lemma angle_bounds {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) (j : Fin N) :
    0 ≤ angle c u p j ∧ angle c u p j ≤ 1 / Real.sqrt u := by
  have hx := factor_real_pos hc hu hp.1 j
  have hb := imaginary_bounds hu hp
  have hs := Real.sqrt_pos.2 hu
  have hss := Real.sq_sqrt hu.le
  have hratio : stripImaginary u p / (u + p + c j) ≤ 1 / Real.sqrt u := by
    have hxu : u ≤ u + p + c j := by linarith [hp.1, hc j]
    calc
      stripImaginary u p / (u + p + c j) ≤ stripImaginary u p / u :=
        div_le_div_of_nonneg_left hb.1 hu hxu
      _ ≤ 1 / Real.sqrt u := by
        apply (div_le_div_iff₀ hu hs).2
        have hm := mul_le_mul_of_nonneg_right hb.2 hs.le
        nlinarith
  have hnonneg := div_nonneg hb.1 hx.le
  exact ⟨Real.arctan_nonneg.2 hnonneg,
    (Real.arctan_le_self hnonneg).trans hratio⟩

private lemma totalAngle_bounds {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) :
    0 ≤ totalAngle c u p ∧ totalAngle c u p ≤ (N : ℝ) / Real.sqrt u := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => (angle_bounds hc hu hp j).1)
  · have h := Finset.sum_le_sum (s := Finset.univ)
      (fun j _ => (angle_bounds hc hu hp j).2)
    simpa [totalAngle, div_eq_mul_inv] using h

private theorem augmented_angle_mem {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) (j : Fin N) :
    totalAngle c u p + angle c u p j ∈ Ico 0 (Real.pi / 2) := by
  have hT := totalAngle_bounds hc hu hp
  have hj := angle_bounds hc hu hp j
  refine ⟨add_nonneg hT.1 hj.1, lt_of_le_of_lt ?_ hsector⟩
  calc
    totalAngle c u p + angle c u p j ≤
        (N : ℝ) / Real.sqrt u + 1 / Real.sqrt u := add_le_add hT.2 hj.2
    _ = ((N : ℝ) + 1) / Real.sqrt u := by ring

private lemma totalAngle_mem {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    totalAngle c u p ∈ Ico 0 (Real.pi / 2) := by
  have hT := totalAngle_bounds hc hu hp
  refine ⟨hT.1, lt_of_le_of_lt hT.2 (lt_trans ?_ hsector)⟩
  exact (div_lt_div_iff_of_pos_right (Real.sqrt_pos.2 hu)).2 (by linarith)

private lemma arg_eq_angle {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    Complex.arg (factor c u p j) = angle c u p j := by
  have hx : 0 < (factor c u p j).re := by
    rw [factor_re]; exact factor_real_pos hc hu hp j
  have ht : Real.tan (Complex.arg (factor c u p j)) =
      stripImaginary u p / (u + p + c j) := by
    rw [Complex.tan_arg, factor_im, factor_re]
  exact (Real.arctan_eq_of_tan_eq ht
    ⟨Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hx),
      Complex.arg_lt_pi_div_two_iff.2 (Or.inl hx)⟩).symm

private lemma factor_inverse_polar {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    (factor c u p j)⁻¹ = ((‖factor c u p j‖⁻¹ : ℝ) : ℂ) *
      Complex.exp (((-angle c u p j : ℝ) : ℂ) * I) := by
  have hpol : ((‖factor c u p j‖ : ℝ) : ℂ) *
      Complex.exp ((angle c u p j : ℂ) * I) = factor c u p j := by
    rw [← arg_eq_angle hc hu hp j]
    exact Complex.norm_mul_exp_arg_mul_I _
  calc
    (factor c u p j)⁻¹ =
        (((‖factor c u p j‖ : ℝ) : ℂ) *
          Complex.exp ((angle c u p j : ℂ) * I))⁻¹ := congrArg Inv.inv hpol.symm
    _ = _ := by
      simp only [mul_inv_rev, ← Complex.exp_neg, Complex.ofReal_inv,
        Complex.ofReal_neg, neg_mul]
      ring

private lemma amplitude_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) :
    0 < amplitude c u p := by
  exact Finset.prod_pos (fun j _ => inv_pos.2
    (norm_pos_iff.2 (factor_ne_zero hc hu hp j)))

private theorem reciprocalProduct_polar {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) :
    reciprocalProduct c u p = (amplitude c u p : ℂ) *
      Complex.exp (((-totalAngle c u p : ℝ) : ℂ) * I) := by
  have hs : (∑ j : Fin N, ((-angle c u p j : ℝ) : ℂ) * I) =
      ((-totalAngle c u p : ℝ) : ℂ) * I := by
    simp only [← Finset.sum_mul, ← Complex.ofReal_sum, Finset.sum_neg_distrib,
      totalAngle]
  calc
    reciprocalProduct c u p = ∏ j : Fin N,
        (((‖factor c u p j‖⁻¹ : ℝ) : ℂ) *
          Complex.exp (((-angle c u p j : ℝ) : ℂ) * I)) := by
      exact Finset.prod_congr rfl (fun j _ => factor_inverse_polar hc hu hp j)
    _ = (∏ j : Fin N, ((‖factor c u p j‖⁻¹ : ℝ) : ℂ)) *
        ∏ j : Fin N, Complex.exp (((-angle c u p j : ℝ) : ℂ) * I) :=
      Finset.prod_mul_distrib
    _ = _ := by rw [← Complex.exp_sum, hs]; simp [amplitude]

private theorem reciprocalProduct_div_polar {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    reciprocalProduct c u p / factor c u p j =
      (‖reciprocalProduct c u p / factor c u p j‖ : ℂ) *
        Complex.exp (((-(totalAngle c u p + angle c u p j) : ℝ) : ℂ) * I) := by
  let a := amplitude c u p * ‖factor c u p j‖⁻¹
  have ha : 0 < a := mul_pos (amplitude_pos hc hu hp)
    (inv_pos.2 (norm_pos_iff.2 (factor_ne_zero hc hu hp j)))
  have he : reciprocalProduct c u p / factor c u p j = (a : ℂ) *
      Complex.exp (((-(totalAngle c u p + angle c u p j) : ℝ) : ℂ) * I) := by
    rw [div_eq_mul_inv, reciprocalProduct_polar hc hu hp,
      factor_inverse_polar hc hu hp j]
    dsimp [a]
    push_cast
    rw [show -(↑(totalAngle c u p) + ↑(angle c u p j)) * I =
      (-↑(totalAngle c u p) * I) + (-↑(angle c u p j) * I) by ring,
      Complex.exp_add]
    ring
  have hn : ‖reciprocalProduct c u p / factor c u p j‖ = a := by
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hn]
  exact he

theorem weight_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    0 < weight c u p := by
  have ht := totalAngle_mem hc hu hp hsector
  have hcos := Real.cos_pos_of_mem_Ioo
    (show totalAngle c u p ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩)
  have he : weight c u p = amplitude c u p * Real.cos (totalAngle c u p) := by
    rw [weight, reciprocalProduct_polar hc hu hp.1]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [he]
  exact mul_pos (amplitude_pos hc hu hp.1) hcos

private lemma hasDerivAt_imaginary_u {u p : ℝ} (hu : 0 < u) (hp : p ≤ 1 / 4) :
    HasDerivAt (fun v : ℝ => stripImaginary v p) (stripImaginary u p / (2 * u)) u := by
  by_cases hb : p = 1 / 4
  · subst p
    simpa [stripImaginary] using (hasDerivAt_const u (0 : ℝ))
  · have hp' : p < 1 / 4 := lt_of_le_of_ne hp hb
    have hrad : u * (1 - 4 * p) ≠ 0 := ne_of_gt (mul_pos hu (by linarith))
    have hd := ((hasDerivAt_id u).mul_const (1 - 4 * p)).sqrt hrad
    have hsq := imaginary_sq hu hp
    have him := imaginary_pos hu hp'
    have he : (1 - 4 * p) / (2 * stripImaginary u p) =
        stripImaginary u p / (2 * u) := by
      apply (div_eq_div_iff (by positivity : 2 * stripImaginary u p ≠ 0)
        (by positivity : 2 * u ≠ 0)).2
      nlinarith
    have hd' : HasDerivAt (fun v : ℝ => stripImaginary v p)
        ((1 - 4 * p) / (2 * stripImaginary u p)) u := by
      simpa [stripImaginary] using hd
    rw [he] at hd'
    exact hd'

private lemma hasDerivAt_imaginary_p {u p : ℝ} (hu : 0 < u) (hp : p < 1 / 4) :
    HasDerivAt (fun q : ℝ => stripImaginary u q) (-2 * u / stripImaginary u p) p := by
  have hrad : u * (1 - 4 * p) ≠ 0 := ne_of_gt (mul_pos hu (by linarith))
  have hlin : HasDerivAt (fun q : ℝ => u * (1 - 4 * q)) (-4 * u) p := by
    convert (((hasDerivAt_id p).const_mul 4).const_sub 1).const_mul u using 1 <;>
      simp [Function.id_def] <;> ring
  have hd := hlin.sqrt hrad
  convert hd using 1 <;>
    simp only [stripImaginary, div_eq_mul_inv, mul_inv_rev] <;> ring

private lemma hasDerivAt_product {N : ℕ} {f : Fin N → ℝ → ℂ} {d : ℂ} {t : ℝ}
    (hf : ∀ j, HasDerivAt (f j) d t) (hn : ∀ j, f j t ≠ 0) :
    HasDerivAt (fun x : ℝ => ∏ j, (f j x)⁻¹)
      (-(∑ j, ((∏ k, (f k t)⁻¹) / f j t) * d)) t := by
  classical
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun j _ => (hf j).inv (hn j))
  convert hd using 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hp := Finset.mul_prod_erase Finset.univ (fun k => (f k t)⁻¹)
    (Finset.mem_univ j)
  rw [← hp]
  simp only [smul_eq_mul, Pi.inv_apply]
  field_simp [hn j] <;> ring

private def derivativeTerm {N : ℕ} (c : Fin N → ℝ) (u p v : ℝ) (j : Fin N) : ℝ :=
  ‖reciprocalProduct c u p / factor c u p j‖ *
    (Real.cos (totalAngle c u p + angle c u p j) +
      v * Real.sin (totalAngle c u p + angle c u p j))

private lemma real_product_derivative {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (v : ℝ) :
    (-(∑ j, (reciprocalProduct c u p / factor c u p j) *
      (1 + (v : ℂ) * I))).re = -∑ j, derivativeTerm c u p v j := by
  simp only [Complex.neg_re, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [reciprocalProduct_div_polar hc hu hp j]
  simp only [Complex.mul_re, Complex.mul_im]
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp [derivativeTerm, Complex.mul_re, Complex.mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg, Real.cos_add, Real.sin_add] <;> ring

private theorem hasDerivAt_weight_u {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Icc 0 (1 / 4)) :
    HasDerivAt (fun v : ℝ => weight c v p)
      (-∑ j, ‖reciprocalProduct c u p / factor c u p j‖ *
        (Real.cos (totalAngle c u p + angle c u p j) +
          (stripImaginary u p / (2 * u)) *
            Real.sin (totalAngle c u p + angle c u p j))) u := by
  have hf : ∀ j, HasDerivAt (fun v : ℝ => factor c v p j)
      (1 + ((stripImaginary u p / (2 * u) : ℝ) : ℂ) * I) u := by
    intro j
    have hr := (((hasDerivAt_id u).add_const p).add_const (c j)).ofReal_comp
    have hi := ((hasDerivAt_imaginary_u hu hp.2).ofReal_comp).mul_const I
    have hsum := hr.add hi
    convert hsum using 1 <;>
      (try funext y) <;>
      simp [factor, Function.comp_def]
  have hF := hasDerivAt_product hf (factor_ne_zero hc hu hp.1)
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hF
  change HasDerivAt (fun v : ℝ => weight c v p)
    (-(∑ j, (reciprocalProduct c u p / factor c u p j) *
      (1 + ((stripImaginary u p / (2 * u) : ℝ) : ℂ) * I))).re u at hR
  rw [real_product_derivative hc hu hp.1] at hR
  exact hR

private theorem hasDerivAt_weight_p {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : p ∈ Ico 0 (1 / 4)) :
    HasDerivAt (fun q : ℝ => weight c u q)
      (-∑ j, ‖reciprocalProduct c u p / factor c u p j‖ *
        (Real.cos (totalAngle c u p + angle c u p j) -
          (2 * u / stripImaginary u p) *
            Real.sin (totalAngle c u p + angle c u p j))) p := by
  have hf : ∀ j, HasDerivAt (fun q : ℝ => factor c u q j)
      (1 + ((-2 * u / stripImaginary u p : ℝ) : ℂ) * I) p := by
    intro j
    have hr := (((hasDerivAt_id p).const_add u).add_const (c j)).ofReal_comp
    have hi := ((hasDerivAt_imaginary_p hu hp.2).ofReal_comp).mul_const I
    have hsum := hr.add hi
    convert hsum using 1 <;>
      (try funext y) <;>
      simp [factor, Function.comp_def]
  have hF := hasDerivAt_product hf (factor_ne_zero hc hu hp.1)
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivAt p hF
  change HasDerivAt (fun q : ℝ => weight c u q)
    (-(∑ j, (reciprocalProduct c u p / factor c u p j) *
      (1 + ((-2 * u / stripImaginary u p : ℝ) : ℂ) * I))).re p at hR
  rw [real_product_derivative hc hu hp.1] at hR
  simpa only [derivativeTerm, neg_mul, neg_div, sub_eq_add_neg] using hR

private lemma quotient_norm_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) (j : Fin N) :
    0 < ‖reciprocalProduct c u p / factor c u p j‖ := by
  apply norm_pos_iff.2
  exact div_ne_zero (Finset.prod_ne_zero_iff.2
    (fun k _ => inv_ne_zero (factor_ne_zero hc hu hp k)))
      (factor_ne_zero hc hu hp j)

private theorem deriv_weight_u_neg {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hN : 0 < N) (hc : ∀ j, 0 ≤ c j) (hu : 0 < u)
    (hp : p ∈ Icc 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    deriv (fun v : ℝ => weight c v p) u < 0 := by
  rw [(hasDerivAt_weight_u hc hu hp).deriv]
  apply neg_neg_of_pos
  apply Finset.sum_pos
  · intro j _
    have ha := augmented_angle_mem hc hu hp hsector j
    have hcos := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ha.1], ha.2⟩
    have hsin := Real.sin_nonneg_of_mem_Icc
      ⟨ha.1, by linarith [Real.pi_pos, ha.2]⟩
    apply mul_pos (quotient_norm_pos hc hu hp.1 j)
    exact add_pos_of_pos_of_nonneg hcos
      (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by positivity)) hsin)
  · exact ⟨⟨0, hN⟩, Finset.mem_univ _⟩

private lemma p_bracket_neg {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hz : ∃ j₀, c j₀ = 0) (hu : 0 < u) (hup : p < u)
    (hp : p ∈ Ico 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) (j : Fin N) :
    Real.cos (totalAngle c u p + angle c u p j) -
      (2 * u / stripImaginary u p) *
        Real.sin (totalAngle c u p + angle c u p j) < 0 := by
  obtain ⟨j₀, hj₀⟩ := hz
  have hpclosed : p ∈ Icc 0 (1 / 4) := ⟨hp.1, hp.2.le⟩
  have hb := imaginary_pos hu hp.2
  have ha := augmented_angle_mem hc hu hpclosed hsector j
  have h0 := angle_bounds hc hu hpclosed j₀
  have hj := angle_bounds hc hu hpclosed j
  have hsum : angle c u p j₀ ≤ totalAngle c u p :=
    Finset.single_le_sum (fun k _ => (angle_bounds hc hu hpclosed k).1)
      (Finset.mem_univ j₀)
  have hle : angle c u p j₀ ≤ totalAngle c u p + angle c u p j := by linarith
  have ht := Real.strictMonoOn_tan.monotoneOn
    (show angle c u p j₀ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], (hle.trans_lt ha.2)⟩)
    (show totalAngle c u p + angle c u p j ∈
        Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], ha.2⟩) hle
  have ht0 : Real.tan (angle c u p j₀) = stripImaginary u p / (u + p) := by
    simp [angle, hj₀, Real.tan_arctan]
  rw [ht0] at ht
  have hratio : stripImaginary u p / (2 * u) < stripImaginary u p / (u + p) := by
    have hup0 : 0 < u + p := by linarith [hu, hp.1]
    apply (div_lt_div_iff₀ (by positivity : 0 < 2 * u)
      hup0).2
    nlinarith [mul_pos hb (sub_pos.2 hup)]
  have htan := hratio.trans_le ht
  have hcos := Real.cos_pos_of_mem_Ioo
    (show totalAngle c u p + angle c u p j ∈
        Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], ha.2⟩)
  rw [Real.tan_eq_sin_div_cos] at htan
  have hm := (div_lt_div_iff₀ (by positivity : 0 < 2 * u) hcos).1 htan
  have hfin : Real.cos (totalAngle c u p + angle c u p j) <
      (2 * u * Real.sin (totalAngle c u p + angle c u p j)) /
        stripImaginary u p := (lt_div_iff₀ hb).2 (by nlinarith)
  rw [show (2 * u * Real.sin (totalAngle c u p + angle c u p j)) /
      stripImaginary u p = (2 * u / stripImaginary u p) *
        Real.sin (totalAngle c u p + angle c u p j) by ring] at hfin
  linarith

private theorem deriv_weight_p_pos {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hz : ∃ j₀, c j₀ = 0) (hu : 0 < u) (hup : p < u)
    (hp : p ∈ Ico 0 (1 / 4))
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    0 < deriv (fun q : ℝ => weight c u q) p := by
  rw [(hasDerivAt_weight_p hc hu hp).deriv, neg_pos]
  apply Finset.sum_neg
  · intro j _
    exact mul_neg_of_pos_of_neg (quotient_norm_pos hc hu hp.1 j)
      (p_bracket_neg hc hz hu hup hp hsector j)
  · obtain ⟨j₀, _⟩ := hz
    exact ⟨j₀, Finset.mem_univ _⟩

private lemma continuousAt_weight_p {N : ℕ} {c : Fin N → ℝ} {u p : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hu : 0 < u) (hp : 0 ≤ p) :
    ContinuousAt (fun q : ℝ => weight c u q) p := by
  have hF : ContinuousAt (fun q : ℝ => reciprocalProduct c u q) p := by
    apply tendsto_finsetProd Finset.univ
    intro j _
    have hfac : ContinuousAt (fun b : ℝ => factor c u b j) p := by
      unfold factor stripImaginary
      fun_prop
    change Filter.Tendsto ((fun b : ℝ => factor c u b j)⁻¹) (𝓝 p)
      (𝓝 ((factor c u p j)⁻¹))
    exact (hfac.inv₀ (factor_ne_zero hc hu hp j)).tendsto
  exact Complex.continuous_re.continuousAt.comp hF

theorem strictAntiOn_weight_u {N : ℕ} {c : Fin N → ℝ} {p : ℝ}
    (hN : 0 < N) (hc : ∀ j, 0 ≤ c j) (hp : p ∈ Icc 0 (1 / 4)) :
    StrictAntiOn (fun u : ℝ => weight c u p) (Ioi (threshold N)) := by
  have hparam : ∀ u ∈ Ioi (threshold N), 0 < u ∧
      ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2 := by
    intro u hu
    have hT : 0 ≤ threshold N := by unfold threshold; positivity
    have hu0 : 0 < u := lt_of_le_of_lt hT hu
    have hs := Real.sqrt_pos.2 hu0
    have hq : 0 < 2 * ((N : ℝ) + 1) / Real.pi := by positivity
    have hsq : (2 * ((N : ℝ) + 1) / Real.pi) ^ 2 = threshold N := by
      unfold threshold; ring
    have hroot : 2 * ((N : ℝ) + 1) / Real.pi < Real.sqrt u := by
      apply (Real.lt_sqrt hq.le).2
      have hbound : (2 * ((N : ℝ) + 1) / Real.pi) ^ 2 < u := by
        rw [hsq]; exact hu
      exact hbound
    have hmul := (div_lt_iff₀ Real.pi_pos).1 hroot
    refine ⟨hu0, (div_lt_iff₀ hs).2 ?_⟩
    nlinarith
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro u hu
    exact (hasDerivAt_weight_u hc (hparam u hu).1 hp).continuousAt.continuousWithinAt
  · intro u hu
    have humem := interior_subset hu
    exact deriv_weight_u_neg hN hc (hparam u humem).1 hp (hparam u humem).2

theorem strictMonoOn_weight_p {N : ℕ} {c : Fin N → ℝ} {u : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hz : ∃ j₀, c j₀ = 0)
    (hu : 0 < u)
    (hsector : ((N : ℝ) + 1) / Real.sqrt u < Real.pi / 2) :
    StrictMonoOn (weight c u) (Icc 0 (1 / 4)) := by
  have hN : 0 < N := by
    obtain ⟨j₀, _⟩ := hz
    exact lt_of_le_of_lt (Nat.zero_le j₀.val) j₀.isLt
  have hNc : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from hN)
  have hs := Real.sqrt_pos.2 hu
  have hmul := (div_lt_iff₀ hs).1 hsector
  have hroot : 1 < Real.sqrt u := by
    by_contra hn
    have hprod := mul_le_mul_of_nonneg_left (le_of_not_gt hn)
      (by positivity : 0 ≤ Real.pi / 2)
    nlinarith [Real.pi_lt_four]
  have huone : (1 : ℝ) < u := by
    have h := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).1 hroot
    simpa using h
  have huquarter : (1 / 4 : ℝ) < u := lt_trans (by norm_num) huone
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro p hp
    exact (continuousAt_weight_p hc hu hp.1).continuousWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact deriv_weight_p_pos hc hz hu (lt_trans hp.2 huquarter)
      ⟨hp.1.le, hp.2⟩ hsector

/- Simultaneous conjugation is valid for every real imaginary part, including zero. -/
private theorem reciprocalProduct_signed_conj {N : ℕ} (c : Fin N → ℝ) (x b : ℝ) :
    (∏ j : Fin N, (((x + c j : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * I)⁻¹) =
      star (∏ j : Fin N, (((x + c j : ℝ) : ℂ) + (b : ℂ) * I)⁻¹) := by
  simp only [Complex.star_def, map_prod, map_inv₀, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, mul_neg, neg_mul]

theorem real_product_signed_reduction {N : ℕ} (c : Fin N → ℝ) (u p b : ℝ)
    (hb : b ^ 2 = u * (1 - 4 * p)) :
    (∏ j : Fin N, (((u + p + c j : ℝ) : ℂ) + (b : ℂ) * I)⁻¹).re =
      weight c u p := by
  have hrad : 0 ≤ u * (1 - 4 * p) := by rw [← hb]; positivity
  have hs : stripImaginary u p ^ 2 = u * (1 - 4 * p) := Real.sq_sqrt hrad
  have hsign : b = stripImaginary u p ∨ b = -stripImaginary u p := by
    exact sq_eq_sq_iff_eq_or_eq_neg.1 (hb.trans hs.symm)
  rcases hsign with h | h
  · subst b; rfl
  · rw [h, reciprocalProduct_signed_conj c (u + p) (stripImaginary u p)]
    simp only [Complex.star_def, Complex.conj_re]
    rfl


end H14Sector

end D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
