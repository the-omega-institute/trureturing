/- GID: D5/S3/Weil/Analytic/NymanFixedRationalKernelLipschitz
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanFixedRationalKernelLipschitz
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global Lipschitz bound for the compact cubic kernel. -/

import D5.S3.Weil.Analytic.NymanFixedRationalKernel
import Mathlib.Tactic
import OmegaBuild.Commands

/-! Global Lipschitz bound for the compact cubic kernel. -/

compile_only_with_mathlib

set_option autoImplicit false
noncomputable section
open Finset Filter Complex ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius

namespace NymanFixedRationalKernel

private def clamp (x : ℝ) : ℝ := max 1 (min x 2)

private theorem clamp_mem (x : ℝ) : clamp x∈Set.Icc (1:ℝ) 2 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩

private theorem clamp_eq {x : ℝ} (hx : x∈Set.Icc (1:ℝ) 2) : clamp x=x := by
  simp [clamp,min_eq_left hx.2,max_eq_right hx.1]

private theorem clamp_lip : LipschitzWith 1 clamp :=
  (LipschitzWith.id.min_const (2:ℝ)).const_max 1

private theorem cube_difference {a d : ℝ} (ha : 0≤a) (ha1 : a≤1) (hd : 0≤d) (hd1 : d≤1) :
    |a^3-d^3|≤3*|a-d| := by
  rw [show a^3-d^3=(a-d)*(a^2+a*d+d^2) by ring,abs_mul,abs_of_nonneg (show 0≤a^2+a*d+d^2 by positivity)]
  rw [mul_comm 3]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have ha2 : a^2≤1 := by nlinarith
  have hd2 : d^2≤1 := by nlinarith
  have had : a*d≤1 := by nlinarith [mul_le_mul_of_nonneg_right ha1 hd]
  linarith

private theorem piece_difference {x y : ℝ} (hx : x∈Set.Icc (1:ℝ) 2) (hy : y∈Set.Icc (1:ℝ) 2)
    (j : Fin 5) :
    |(max (x/A^j.val-1) 0)^3-(max (y/A^j.val-1) 0)^3|≤3*|x-y| := by
  have hp : 1≤A^j.val := one_le_pow₀ one_lt_A.le
  have hpos : 0<A^j.val := by positivity
  have hbound (u : ℝ) (hu : u∈Set.Icc (1:ℝ) 2) : max (u/A^j.val-1) 0≤1 := by
    apply max_le _ (by norm_num)
    have hdiv : u/A^j.val≤2 := (div_le_iff₀ hpos).2 (hu.2.trans (by linarith))
    linarith
  apply (cube_difference (le_max_right _ _) (hbound x hx) (le_max_right _ _) (hbound y hy)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ |(x/A^j.val-1)-(y/A^j.val-1)| := abs_max_sub_max_le_abs _ _ _
    _ = |x-y|/A^j.val := by
      rw [show x/A^j.val-1-(y/A^j.val-1)=(x-y)/A^j.val by ring,
        abs_div,abs_of_pos hpos]
    _ ≤ |x-y| := (div_le_iff₀ hpos).2 (le_mul_of_one_le_right (abs_nonneg _) hp)

private theorem b_local_lip :
    ∃ K : ℝ, 0≤K ∧ ∀ x∈Set.Icc (1:ℝ) 2,∀ y∈Set.Icc (1:ℝ) 2, |b x-b y|≤K*|x-y| := by
  refine ⟨(∑ j:Fin 5,|c j| * 3)/6,by positivity,?_⟩
  intro x hx y hy
  unfold b
  rw [←sub_div,abs_div,abs_of_nonneg (by norm_num : 0≤(6:ℝ)),←sum_sub_distrib]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<6)).2
  calc
    _ = |∑ j:Fin 5,c j*((max (x/A^j.val-1) 0)^3-(max (y/A^j.val-1) 0)^3)| := by
      congr 1
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j:Fin 5,|c j*((max (x/A^j.val-1) 0)^3-(max (y/A^j.val-1) 0)^3)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.univ:Finset (Fin 5)) (fun j : Fin 5 => c j*((max (x/A^j.val-1) 0)^3-(max (y/A^j.val-1) 0)^3))
    _ ≤ ∑ j:Fin 5,|c j| * (3*|x-y|) := by
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (piece_difference hx hy j) (abs_nonneg _)
    _ = _ := by
      simp_rw [←mul_assoc,←sum_mul]
      ring

private theorem b_clamp (x : ℝ) : b (clamp x)=b x := by
  by_cases hx : x∈Set.Icc (1:ℝ) 2
  · rw [clamp_eq hx]
  · have hh : x<1 ∨ 2<x := by by_contra! h; exact hx h
    rcases hh with h|h
    · have hc : clamp x=1 := by simp [clamp,max_eq_left ((min_le_left _ _).trans h.le)]
      rw [hc,b_zero_left (by norm_num),b_zero_left h.le]
    · have hc : clamp x=2 := by simp [clamp,min_eq_right h.le]
      rw [hc,b_zero_right A4_lt_two.le,b_zero_right (A4_lt_two.le.trans h.le)]

theorem b_lipschitz :
    ∃ K : ℝ, 0≤K ∧ ∀ x y : ℝ,|b x-b y|≤K*|x-y| := by
  obtain ⟨K,hK,h⟩ := b_local_lip
  refine ⟨K,hK,?_⟩
  intro x y
  have hl := h (clamp x) (clamp_mem x) (clamp y) (clamp_mem y)
  rw [b_clamp,b_clamp] at hl
  have hc := clamp_lip.dist_le_mul x y
  rw [Real.dist_eq,Real.dist_eq] at hc
  norm_num at hc
  exact hl.trans (mul_le_mul_of_nonneg_left hc hK)

end NymanFixedRationalKernel
