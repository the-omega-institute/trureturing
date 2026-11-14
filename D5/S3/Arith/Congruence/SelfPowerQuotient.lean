/- GID: D5/S3/Arith/Congruence/SelfPowerQuotient
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/SelfPowerQuotient
   mirror-E: none
   anchors: []
   utility: none
   digest: Exact integrality of the self-power quotient in OEIS A081215. -/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

namespace D5.S3.Arith.Congruence.SelfPowerQuotient

/-- The numerator in Englander's definition of OEIS A081215. -/
def numerator (n : ℕ) : ℤ := (n : ℤ) ^ (n + 1) + (-1 : ℤ) ^ n

/-- Integer division, proved exact by `exact_quotient`. -/
def a (n : ℕ) : ℤ := numerator n / ((n : ℤ) + 1) ^ 2

/-- A twice-integrated geometric sum, with integer coefficients. -/
def tail (j : ℕ) (y : ℤ) : ℤ :=
  ∑ i ∈ Finset.range j, ∑ r ∈ Finset.range i, y ^ r

private theorem tail_mul (j : ℕ) (y : ℤ) :
    tail j y * (y - 1) = (∑ i ∈ Finset.range j, y ^ i) - j := by
  unfold tail
  rw [Finset.sum_mul]
  simp only [geom_sum_mul]
  simp [Finset.sum_sub_distrib]

private theorem tail_square (j : ℕ) (y : ℤ) :
    tail j y * (y - 1) ^ 2 = y ^ j - 1 - (j : ℤ) * (y - 1) := by
  have h := congrArg (fun z : ℤ => z * (y - 1)) (tail_mul j y)
  rw [sub_mul, geom_sum_mul] at h
  nlinarith [h]

/-- A division-free integer expression for the exact quotient. -/
theorem quotient_tail (n : ℕ) :
    a n = (-1 : ℤ) ^ n * (1 - tail (n + 1) (-(n : ℤ))) := by
  have ht := tail_square (n + 1) (-(n : ℤ))
  have hs : ((-1 : ℤ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hp : (-(n : ℤ)) ^ (n + 1) =
      -((-1 : ℤ) ^ n * (n : ℤ) ^ (n + 1)) := by
    rw [neg_eq_neg_one_mul, mul_pow, pow_succ (-1 : ℤ)]
    ring
  rw [hp] at ht
  push_cast at ht
  have he : numerator n = ((n : ℤ) + 1) ^ 2 *
      ((-1 : ℤ) ^ n * (1 - tail (n + 1) (-(n : ℤ)))) := by
    dsimp [numerator]
    linear_combination (-1 : ℤ) ^ n * ht - (n : ℤ) ^ (n + 1) * hs
  unfold a
  rw [he, Int.mul_ediv_cancel_left]
  positivity

/-- Exact quotient identity; hence no truncation is involved. -/
theorem exact_quotient (n : ℕ) :
    ((n : ℤ) + 1) ^ 2 * a n = numerator n := by
  rw [quotient_tail]
  have ht := tail_square (n + 1) (-(n : ℤ))
  have hs : ((-1 : ℤ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hp : (-(n : ℤ)) ^ (n + 1) =
      -((-1 : ℤ) ^ n * (n : ℤ) ^ (n + 1)) := by
    rw [neg_eq_neg_one_mul, mul_pow, pow_succ (-1 : ℤ)]
    ring
  rw [hp] at ht
  push_cast at ht
  dsimp [numerator]
  linear_combination -((-1 : ℤ) ^ n) * ht + (n : ℤ) ^ (n + 1) * hs

#print axioms quotient_tail
#print axioms exact_quotient
end D5.S3.Arith.Congruence.SelfPowerQuotient
