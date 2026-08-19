/- GID: D5/S3/Constants/Irrationality/TribonacciIrrationality
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/TribonacciIrrationality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Tribonacci constant is irrational, being a non-integer algebraic integer. -/

import D5.S0.Tower.Tribonacci.Values
import Mathlib.NumberTheory.Real.Irrational

/- Library-search audit trail (2026-08-18):
   * Searched the repository for the object, not the name: `Irrational` appears in
     twenty-six D5 files and none of them concerns the Tribonacci constant.  The
     quadratic base of the non-Pisot frontier has `beta13_irrational`; the cubic
     constant has nothing.
   * Pinned Mathlib's `irrational_nrt_of_notint_nrt` covers n-th roots, not a
     general cubic, so it does not apply.  `Rat.den_eq_one_iff` and the integer
     bound below are what the elementary route needs.
   * The three inputs are already in the tree: the defining cubic, and the two
     bounds placing the constant strictly between one and two. -/

namespace D5.S3.Constants.Irrationality.TribonacciIrrationality

open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant

/-- A rational satisfying the Tribonacci cubic has denominator one: the cubic is
monic with integer coefficients, so its rational roots are integers. -/
theorem cubic_rational_root_is_integer (q : Rat)
    (hq : (q : Real) ^ 3 = (q : Real) ^ 2 + (q : Real) + 1) : q.den = 1 := by
  have hcast : q ^ 3 = q ^ 2 + q + 1 := by exact_mod_cast hq
  have hd : ((q.den : Rat)) ≠ 0 := by exact_mod_cast q.den_nz
  have hkey : (q.num : Int) ^ 3 =
      q.num ^ 2 * (q.den : Int) + q.num * (q.den : Int) ^ 2 + (q.den : Int) ^ 3 := by
    have hnum : (q.num : Rat) = q * (q.den : Rat) := by
      have hdiv : (q.num : Rat) / (q.den : Rat) = q := Rat.num_div_den q
      field_simp at hdiv
      linarith [hdiv]
    have hmul : (q.num : Rat) ^ 3 =
        (q.num : Rat) ^ 2 * (q.den : Rat) + (q.num : Rat) * (q.den : Rat) ^ 2
          + (q.den : Rat) ^ 3 := by
      rw [hnum]
      have h3 : (q * (q.den : Rat)) ^ 3 = q ^ 3 * (q.den : Rat) ^ 3 := by ring
      rw [h3, hcast]
      ring
    exact_mod_cast hmul
  have hdvd : (q.den : Int) ∣ q.num ^ 3 :=
    ⟨q.num ^ 2 + q.num * (q.den : Int) + (q.den : Int) ^ 2, by rw [hkey]; ring⟩
  have hdvd_nat : q.den ∣ q.num.natAbs ^ 3 := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_pow] using this
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hcop3 : Nat.Coprime (q.num.natAbs ^ 3) q.den := hcop.pow_left 3
  exact Nat.eq_one_of_dvd_coprimes hcop3 hdvd_nat dvd_rfl

/-- The Tribonacci constant is irrational. -/
theorem tribonacciConstant_irrational : Irrational t := by
  rintro ⟨q, hq⟩
  have hcubic : (q : Real) ^ 3 = (q : Real) ^ 2 + (q : Real) + 1 := by
    rw [hq]; exact tribonacciConstant_cubic
  have hden := cubic_rational_root_is_integer q hcubic
  have hint : (q.num : Rat) = q := Rat.coe_int_num_of_den_eq_one hden
  have hlow : (1 : Real) < (q : Real) := by rw [hq]; exact one_lt_tribonacciConstant
  have hhigh : (q : Real) < 2 := by rw [hq]; exact tribonacciConstant_lt_two
  have hq1 : (1 : Rat) < q := by exact_mod_cast hlow
  have hq2 : q < 2 := by exact_mod_cast hhigh
  have h1 : (1 : Int) < q.num := by
    have : (1 : Rat) < (q.num : Rat) := by rw [hint]; exact hq1
    exact_mod_cast this
  have h2 : q.num < 2 := by
    have : (q.num : Rat) < 2 := by rw [hint]; exact hq2
    exact_mod_cast this
  omega

#print axioms tribonacciConstant_irrational

end D5.S3.Constants.Irrationality.TribonacciIrrationality
