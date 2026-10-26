/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFiveConstants
   mirror-E: none(waiver:coefficient-asymptotics)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Pi.Wallis]
   utility: none
   digest: The rational coefficient constant and its strict Wallis gap. -/

import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Data.Nat.Choose.Sum

/-! Finite subset integration computes the source numerator constant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants

open Finset Real intervalIntegral MeasureTheory
open scoped BigOperators Topology

/-- The odd denominator product in the rational coefficient constant. -/
noncomputable def oddProd (h : ℕ) : ℝ := ∏ i ∈ range h, (2*(i : ℝ)+1)

/-- The corresponding even numerator product. -/
noncomputable def evenProd (h : ℕ) : ℝ := ∏ i ∈ range h, (2*(i : ℝ)+2)

/-- Leading constant of the rational part after normalization by `n^h`. -/
noncomputable def rationalConstant (h : ℕ) : ℝ :=
  (∏ i ∈ range (h-1), (2*(i : ℝ)+2)/(2*i+3)) / ((h.factorial : ℝ)*oddProd h)

/-- Leading upper constant of the Gauss part after the even geometric convolutions. -/
noncomputable def productConstant (h : ℕ) : ℝ :=
  Real.pi / (2^(h+1)*(h.factorial : ℝ)^2)

private theorem subset_integral {α : Type} (s : Finset α) :
    (∑ S ∈ s.powerset, (-1 : ℝ)^S.card / (2*S.card+1)) =
      ∫ x in (0 : ℝ)..1, (1-x^2)^s.card := by
  classical
  have heq (x : ℝ) : (1-x^2)^s.card =
      ∑ S ∈ s.powerset, (-1 : ℝ)^S.card*x^(2*S.card) := by
    rw [← prod_const, prod_sub]
    apply sum_congr rfl
    intro S _
    simp only [prod_const_one, mul_one, prod_const, ← pow_mul, mul_comm 2]
  rw [show (fun x : ℝ => (1-x^2)^s.card) =
    (fun x => ∑ S ∈ s.powerset, (-1 : ℝ)^S.card*x^(2*S.card)) from funext heq,
    intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro S _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  · intro S _
    apply Continuous.intervalIntegrable
    fun_prop

private theorem one_sub_sq_integral (p : ℕ) :
    (∫ x in (0 : ℝ)..1, (1-x^2)^p) =
      ∏ i ∈ range p, (2*(i : ℝ)+2)/(2*i+3) := by
  have hcont : Continuous (fun x : ℝ => (1-x^2)^p) := by fun_prop
  have heven : (∫ x in (-1 : ℝ)..0, (1-x^2)^p) =
      ∫ x in (0 : ℝ)..1, (1-x^2)^p := by
    have h := integral_comp_mul_right (fun x : ℝ => (1-x^2)^p)
      (a := (-1 : ℝ)) (b := 0) (c := (-1 : ℝ)) (by norm_num)
    simpa only [mul_neg_one, neg_sq, zero_mul, neg_zero, inv_neg, inv_one,
      neg_one_smul, integral_symm (0 : ℝ) 1, neg_neg] using h
  have hsplit := integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)
  have hsin := integral_sin_pow_odd_mul_cos_pow p 0 (a := 0) (b := Real.pi)
  simp only [pow_zero, mul_one, one_mul, cos_pi, cos_zero] at hsin
  rw [integral_sin_pow_odd] at hsin
  rw [heven] at hsplit
  linarith

/-- The alternating subset constant depends only on the number of offsets. -/
theorem subset_constant {α : Type} (s : Finset α) :
    (∑ S ∈ s.powerset, (-1 : ℝ)^S.card / (2*S.card+1)) =
      ∏ i ∈ range s.card, (2*(i : ℝ)+2)/(2*i+3) := by
  rw [subset_integral, one_sub_sq_integral]

private theorem evenProd_factorial (h : ℕ) : evenProd h = 2^h*(h.factorial : ℝ) := by
  induction h with
  | zero => simp [evenProd]
  | succ h ih =>
    rw [evenProd, prod_range_succ]
    change evenProd h * _ = _
    rw [ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

private theorem ratio_W (h : ℕ) : (evenProd h / oddProd h)^2 =
    (2*(h : ℝ)+1)*Real.Wallis.W h := by
  induction h with
  | zero => norm_num [evenProd, oddProd, Real.Wallis.W]
  | succ h ih =>
    rw [evenProd, oddProd, prod_range_succ, prod_range_succ]
    change ((evenProd h*(2*(h : ℝ)+2))/(oddProd h*(2*(h : ℝ)+1)))^2 = _
    rw [← div_mul_div_comm, mul_pow, ih, Real.Wallis.W_succ]
    push_cast
    have hh : 2*(h : ℝ)+1 ≠ 0 := by positivity
    have hh' : 2*(h : ℝ)+3 ≠ 0 := by positivity
    field_simp
    <;> ring

private theorem rational_constant_ratio (h : ℕ) (hh : 1 ≤ h) :
    rationalConstant h = (evenProd h / oddProd h)^2 /
      ((h : ℝ)*(2*2^h*(h.factorial : ℝ)^2)) := by
  have hop : 0 < oddProd h := prod_pos (fun i _ => by positivity)
  have hfact : (h.factorial : ℝ) ≠ 0 := by positivity
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  have hodd : oddProd h = ∏ i ∈ range (h-1), (2*(i : ℝ)+3) := by
    have heq := prod_range_succ' (fun i : ℕ => (2*(i : ℝ)+1)) (h-1)
    rw [show h-1+1=h by omega] at heq
    simpa [oddProd, Nat.cast_add, Nat.cast_one, mul_add, add_assoc, show (2 : ℝ)+1=3 by norm_num] using heq
  have hev : evenProd h = evenProd (h-1)*(2*(h : ℝ)) := by
    unfold evenProd
    rw [show h = (h-1)+1 by omega, prod_range_succ]
    push_cast
    have hc : ((h-1 : ℕ) : ℝ) = (h : ℝ)-1 := by
      rw [Nat.cast_sub hh]; norm_num
    rw [hc]
    ring
  unfold rationalConstant
  rw [prod_div_distrib, ← hodd]
  change (evenProd (h-1)/oddProd h)/((h.factorial : ℝ)*oddProd h) = _
  have he := evenProd_factorial h
  field_simp
  calc _ = (evenProd (h-1)*(2*(h : ℝ)))*(2^h*(h.factorial : ℝ)) := by ring
       _ = evenProd h * evenProd h := by rw [← hev, ← he]
       _ = _ := by ring

/-- Every admissible parameter height has a strictly positive leading coefficient gap. -/
theorem leading_gap_pos (h : ℕ) (hh : 1 ≤ h) :
    0 < rationalConstant h - productConstant h := by
  have hR : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have hW := Real.Wallis.le_W h
  have hratio := ratio_W h
  have hden : 0 < 2*(h : ℝ)+2 := by positivity
  have hden' : 0 < 2*(h : ℝ)+1 := by positivity
  have hb := mul_le_mul_of_nonneg_right hW (le_of_lt hden')
  have hstrict : Real.pi*(h : ℝ) < (evenProd h / oddProd h)^2 := by
    rw [mul_comm (Real.Wallis.W h), ← hratio] at hb
    have hb' : (2*(h : ℝ)+1)^2*Real.pi ≤
        (evenProd h / oddProd h)^2*(4*(h : ℝ)+4) := by
      have hz := (div_le_iff₀ hden).mp
        (show ((2*(h : ℝ)+1)*(Real.pi/2)*(2*(h : ℝ)+1))/(2*(h : ℝ)+2) ≤
          (evenProd h / oddProd h)^2 from by convert hb using 1 <;> ring)
      nlinarith
    nlinarith [Real.pi_pos]
  rw [rational_constant_ratio h hh, productConstant]
  rw [show (2 : ℝ)^(h+1) = 2*2^h by rw [pow_succ]; ring]
  have hhp : (0 : ℝ) < h := by exact_mod_cast hh
  have hc : 0 < 2*2^h*(h.factorial : ℝ)^2 := by positivity
  apply sub_pos.mpr
  rw [div_lt_div_iff₀ hc (mul_pos hhp hc)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using mul_lt_mul_of_pos_right hstrict hc

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiFiveConstants
