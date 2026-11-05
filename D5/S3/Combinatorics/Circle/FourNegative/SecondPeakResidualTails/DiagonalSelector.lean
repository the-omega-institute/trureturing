import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.MaskInventory
import Mathlib.Data.Int.DivMod

/-! Prepared residual construction.  The signed selector is the corrected selector in
   uxwv-lowest-diagonal-complement-selector-20261102.py.  All subtraction
   inside the selector and its numerator is in integers. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

def diagonalV (z h : ℤ) : ℤ := 1 + (-3 * (h / 4) - 7 * (z / 8) - 1) % (z + 1)
def diagonalS (z h : ℤ) : ℤ := 4 * diagonalV z h
def diagonalRInt (z h : ℤ) : ℤ := h - diagonalS z h
def diagonalNumerator (z h : ℤ) : ℤ :=
  (4*z+1)*h + (2*z+1)*diagonalS z h - 7*z/2
def diagonalAlphaInt (z h : ℤ) : ℤ := diagonalNumerator z h / (4*(z+1))

/-- The quotient has an explicit integral witness.  In particular the
denominator is 4(z+1), and the subtracted term is exactly 7z/2. -/
theorem diagonal_selector_integral (z h : ℤ) (hz8 : (8 : ℤ) ∣ z)
    (hh4 : (4 : ℤ) ∣ h) :
    4*(z+1) * diagonalAlphaInt z h =
      (4*z+1)*h + (2*z+1)*diagonalS z h - 7*z/2 := by
  let k := (-3*(h/4)-7*(z/8)-1) / (z+1)
  have hzEq : 8*(z/8) = z := Int.mul_ediv_cancel' hz8
  have hhEq : 4*(h/4) = h := Int.mul_ediv_cancel' hh4
  have hhalf : 7*z/2 = 28*(z/8) := by
    apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
    linear_combination -7 * hzEq
  have hdivision := Int.emod_add_mul_ediv (-3*(h/4)-7*(z/8)-1) (z+1)
  have hv : diagonalV z h = -3*(h/4)-7*(z/8)-(z+1)*k := by
    dsimp only [diagonalV, k]
    linear_combination hdivision
  have hsmall : (4*z+1)*(h/4)+(2*z+1)*diagonalV z h-7*(z/8) =
      (z+1)*(4*(h/4)+2*diagonalV z h+k) := by
    linear_combination -hv
  have hnum : diagonalNumerator z h =
      4*(z+1)*(4*(h/4)+2*diagonalV z h+k) := by
    calc
      diagonalNumerator z h =
          4*((4*z+1)*(h/4)+(2*z+1)*diagonalV z h-7*(z/8)) := by
        dsimp only [diagonalNumerator, diagonalS]
        rw [hhalf]
        linear_combination -(4*z+1)*hhEq
      _ = 4*(z+1)*(4*(h/4)+2*diagonalV z h+k) := by rw [hsmall]; ring
  have hdvd : 4*(z+1) ∣ diagonalNumerator z h :=
    ⟨4*(h/4)+2*diagonalV z h+k, hnum⟩
  exact Int.mul_ediv_cancel' hdvd

theorem diagonal_selector_bounds (z h : ℤ) (hz : 8 ≤ z) (hh : 8*z ≤ h) :
    4 ≤ diagonalS z h ∧ diagonalS z h ≤ 4*(z+1) ∧
    4*(z+1) < h ∧ 0 < diagonalRInt z h ∧ diagonalRInt z h < h := by
  have hm : 0 < z+1 := by omega
  have hlo := Int.emod_nonneg (-3*(h/4)-7*(z/8)-1) (ne_of_gt hm)
  have hhi := Int.emod_lt_of_pos (-3*(h/4)-7*(z/8)-1) hm
  dsimp only [diagonalRInt, diagonalS, diagonalV]
  omega

theorem diagonal_alpha_bounds (z h : ℤ) (hz : 8 ≤ z) (hh : 8*z ≤ h)
    (hz8 : (8 : ℤ) ∣ z) (hh4 : (4 : ℤ) ∣ h) :
    0 ≤ diagonalAlphaInt z h ∧ diagonalAlphaInt z h < z*h := by
  have hs := diagonal_selector_bounds z h hz hh
  have heq := diagonal_selector_integral z h hz8 hh4
  have hden : 0 < 4*(z+1) := by omega
  have hhalf0 : 0 ≤ 7*z/2 := Int.ediv_nonneg (by omega) (by norm_num)
  have hhalf1 : 7*z/2 ≤ 4*z := by omega
  have hzh : 0 ≤ z*h := mul_nonneg (by omega) (by omega)
  have hterm : 0 ≤ (2*z+1)*diagonalS z h := mul_nonneg (by omega) (by omega)
  have hnum0 : 0 < diagonalNumerator z h := by
    dsimp only [diagonalNumerator]
    nlinarith only [hz, hh, hzh, hterm, hhalf1]
  have ha0 : 0 ≤ diagonalAlphaInt z h := by
    dsimp only [diagonalAlphaInt]
    exact Int.ediv_nonneg hnum0.le hden.le
  have hbracket : 0 < (2*z-1)*h-diagonalS z h := by
    have hm := mul_nonneg (show 0 ≤ 2*z-2 by omega) (show 0 ≤ h by omega)
    have hSh : diagonalS z h < h := lt_of_le_of_lt hs.2.1 hs.2.2.1
    nlinarith only [hm, hSh]
  have hdiff : 0 < (2*z+1)*((2*z-1)*h-diagonalS z h) :=
    mul_pos (by omega) hbracket
  have hnum1 : diagonalNumerator z h < 4*(z+1)*(z*h) := by
    dsimp only [diagonalNumerator]
    nlinarith only [hdiff, hhalf0]
  refine ⟨ha0, (mul_lt_mul_iff_right₀ hden).mp ?_⟩
  simpa only [heq, diagonalNumerator] using hnum1

/-- Natural masks are formed only after proving the signed quantities
nonnegative.  The cast equations are retained for the later mass consumer. -/
theorem diagonal_tail_transport (z h : ℕ) (hz : 8 ≤ z) (hh : 8*z ≤ h)
    (hz8 : 8 ∣ z) (hh4 : 4 ∣ h) :
    let alpha := (diagonalAlphaInt (z : ℤ) (h : ℤ)).toNat
    let R := (diagonalRInt (z : ℤ) (h : ℤ)).toNat
    alpha < z*h ∧ R < h ∧
      (alpha : ℤ) = diagonalAlphaInt (z : ℤ) (h : ℤ) ∧
      (R : ℤ) = diagonalRInt (z : ℤ) (h : ℤ) := by
  have hz' : (8 : ℤ) ≤ (z : ℤ) := by exact_mod_cast hz
  have hh' : 8*(z : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
  have hz8' : (8 : ℤ) ∣ (z : ℤ) := by exact_mod_cast hz8
  have hh4' : (4 : ℤ) ∣ (h : ℤ) := by exact_mod_cast hh4
  have ha := diagonal_alpha_bounds (z : ℤ) (h : ℤ) hz' hh' hz8' hh4'
  have hs := diagonal_selector_bounds (z : ℤ) (h : ℤ) hz' hh'
  dsimp only
  have hca := Int.toNat_of_nonneg ha.1
  have hcr := Int.toNat_of_nonneg hs.2.2.2.1.le
  refine ⟨?_, ?_, hca, hcr⟩
  · exact_mod_cast (show
        ((diagonalAlphaInt (z : ℤ) (h : ℤ)).toNat : ℤ) < (z : ℤ)*(h : ℤ) from
      by rw [hca]; exact ha.2)
  · exact_mod_cast (show
        ((diagonalRInt (z : ℤ) (h : ℤ)).toNat : ℤ) < (h : ℤ) from
      by rw [hcr]; exact hs.2.2.2.2)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
