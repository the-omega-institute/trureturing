/- GID: D5/S3/ArithUnits/HalfFactorial
   generality: G
   mirror-B: D5/B/S3/ArithUnits/HalfFactorial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A half-factorial gives the square-root criterion for minus one modulo a prime. -/

import D5.S3.Arith.Wilson
import Mathlib.Data.ZMod.Factorial
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace D5.S3.ArithUnits.HalfFactorial

/-- For every prime, including two, splitting the nonzero residue product at
`(p - 1) / 2` expresses Wilson's factorial as a signed square. -/
theorem factorial_eq_sign_mul_half_factorial_sq (p : Nat) (hp : p.Prime) :
    (Nat.factorial (p - 1) : ZMod p) =
      (-1 : ZMod p) ^ ((p - 1) / 2) *
        (Nat.factorial ((p - 1) / 2) : ZMod p) ^ 2 := by
  rcases hp.eq_two_or_odd' with rfl | hp_odd
  · norm_num
  · have hhalf_le : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
    have hcomplement : (p - 1) - (p - 1) / 2 = (p - 1) / 2 := by
      obtain ⟨k, hk⟩ := hp_odd
      omega
    rw [← Nat.factorial_mul_descFactorial hhalf_le, hcomplement, Nat.cast_mul]
    rw [ZMod.cast_descFactorial (hhalf_le.trans (Nat.sub_le p 1))]
    ring

/-- If `p` is one modulo four, the cast of `((p - 1) / 2)!` is an explicit
square root of minus one modulo `p`. -/
theorem half_factorial_sq_eq_neg_one_of_mod_four_eq_one
    (p : Nat) (hp : p.Prime) (hmod : p % 4 = 1) :
    (Nat.factorial ((p - 1) / 2) : ZMod p) ^ 2 = -1 := by
  have hsign : (-1 : ZMod p) ^ ((p - 1) / 2) = 1 := by
    apply Even.neg_one_pow
    refine ⟨(p - 1) / 4, ?_⟩
    omega
  have hmain := factorial_eq_sign_mul_half_factorial_sq p hp
  rw [hsign, one_mul] at hmain
  exact hmain.symm.trans (D5.S3.Arith.Wilson.wilson_theorem p hp)

/-- If `p` is three modulo four, no residue modulo `p` squares to minus one. -/
theorem not_exists_sq_eq_neg_one_of_mod_four_eq_three
    (p : Nat) (hp : p.Prime) (hmod : p % 4 = 3) :
    ¬ ∃ x : ZMod p, x ^ 2 = -1 := by
  letI := Fact.mk hp
  rintro ⟨x, hx⟩
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one hx hmod

/-- The half-factorial form of the minus-one quadratic-residue criterion:
the signed-square identity, its explicit witness in residue class one modulo
four, and nonexistence in residue class three modulo four. -/
theorem half_factorial_mod_prime (p : Nat) (hp : p.Prime) :
    ((Nat.factorial (p - 1) : ZMod p) =
        (-1 : ZMod p) ^ ((p - 1) / 2) *
          (Nat.factorial ((p - 1) / 2) : ZMod p) ^ 2) ∧
      (p % 4 = 1 → (Nat.factorial ((p - 1) / 2) : ZMod p) ^ 2 = -1) ∧
      (p % 4 = 3 → ¬ ∃ x : ZMod p, x ^ 2 = -1) := by
  exact ⟨factorial_eq_sign_mul_half_factorial_sq p hp,
    half_factorial_sq_eq_neg_one_of_mod_four_eq_one p hp,
    not_exists_sq_eq_neg_one_of_mod_four_eq_three p hp⟩

end D5.S3.ArithUnits.HalfFactorial
