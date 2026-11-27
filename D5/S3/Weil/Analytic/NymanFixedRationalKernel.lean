/- GID: D5/S3/Weil/Analytic/NymanFixedRationalKernel
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanFixedRationalKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact support of the explicit cubic rational kernel. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false

open Finset Complex Set
open scoped BigOperators

namespace NymanFixedRationalKernel

noncomputable section

/-- Rational multiplicative dilation, with fourth power strictly less than 2. -/
def A : ℝ := 7/6

def c : Fin 5 → ℝ := ![1, -(1+A+A^2+A^3), A+A^2+2*A^3+A^4+A^5,
  -(A^3+A^4+A^5+A^6), A^6]

/-- Four multiplicative differences of the cubic positive-part function. -/
def b (u : ℝ) : ℝ := (∑ j : Fin 5, c j * (max (u/A^j.val-1) 0)^3)/6

/-- The exact same finite kernel over rational inputs. -/
def bRat (u : ℚ) : ℚ :=
  let a : ℚ := 7/6
  let d : Fin 5 → ℚ := ![1, -(1+a+a^2+a^3), a+a^2+2*a^3+a^4+a^5,
    -(a^3+a^4+a^5+a^6), a^6]
  (∑ j : Fin 5, d j * (max (u/a^j.val-1) 0)^3)/6

theorem bRat_cast (u : ℚ) : (bRat u : ℝ) = b u := by
  simp [bRat,b,Fin.sum_univ_succ,c,A,Rat.cast_max]

theorem A_pos : 0 < A := by norm_num [A]
theorem one_lt_A : 1 < A := by norm_num [A]
theorem A4_lt_two : A^4 < 2 := by norm_num [A]

theorem continuous_b : Continuous b := by
  unfold b
  fun_prop

/-- Polynomial cancellation at the right endpoint is exact. -/
private theorem raw_cube_cancellation (u : ℝ) : ∑ j : Fin 5, c j * (u/A^j.val-1)^3 = 0 := by
  simp [Fin.sum_univ_succ,c,A]
  ring

theorem b_zero_left {u : ℝ} (hu : u≤1) : b u=0 := by
  unfold b
  rw [show (∑ j : Fin 5, c j * (max (u/A^j.val-1) 0)^3)=0 by
    apply sum_eq_zero
    intro j _
    have ha : 1≤A^j.val := one_le_pow₀ one_lt_A.le
    have hpos : 0<A^j.val := pow_pos A_pos _
    rw [max_eq_right (sub_nonpos.mpr ((div_le_iff₀ hpos).mpr (by simpa using hu.trans ha))) ]
    simp]
  norm_num

theorem b_zero_right {u : ℝ} (hu : A^4≤u) : b u=0 := by
  unfold b
  have he : (∑ j : Fin 5, c j * (max (u/A^j.val-1) 0)^3) =
      ∑ j : Fin 5, c j * (u/A^j.val-1)^3 := by
    apply sum_congr rfl
    intro j _
    have ha : A^j.val≤A^4 := pow_le_pow_right₀ one_lt_A.le (by omega)
    have hpos : 0<A^j.val := pow_pos A_pos _
    rw [max_eq_left (sub_nonneg.mpr ((le_div_iff₀ hpos).mpr (by simpa using ha.trans hu)))]
  rw [he,raw_cube_cancellation]
  norm_num

theorem b_zero_off (u : ℝ) (hu : u∉Ioo (1:ℝ) 2) : b u=0 := by
  by_cases hl : u≤1
  · exact b_zero_left hl
  · exact b_zero_right (A4_lt_two.le.trans (by
      by_contra! hh
      exact hu ⟨lt_of_not_ge hl,hh⟩))

/-- Polynomial in the multiplicative shift whose roots enforce compact support. -/
theorem coefficient_product (z : ℂ) :
    ∑ j : Fin 5, (c j : ℂ)*z^j.val =
      (1-z)*(1-(A:ℂ)*z)*(1-(A:ℂ)^2*z)*(1-(A:ℂ)^3*z) := by
  simp [Fin.sum_univ_succ,c]
  ring

end
end NymanFixedRationalKernel
