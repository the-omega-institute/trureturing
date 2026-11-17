/- GID: D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.claim; result=D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.result; claim=D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation.claim
   digest: The allowed even inputs 2, 4 and 6 refute Englander's full polynomial-existence conjecture. -/
import D5.S3.Arith.Congruence.SelfPowerQuotient
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Arith.Congruence.SelfPowerResiduePolynomialRefutation
open SelfPowerQuotient

/-- Englander's XVII, allowing arbitrary complex coefficients. The first `2*k`
polynomials form one fixed family for all integers `n > k`. -/
def claim : Prop :=
  ∀ k : ℕ, 0 < k → ∃ P : ℕ → Polynomial ℂ,
    (∀ r : ℕ, r < 2*k → (P r).natDegree = k) ∧
    ∀ n : ℕ, k < n →
      (P (n % (2*k))).eval (n : ℂ) =
        ((a n % ((n : ℤ)^k + (-1 : ℤ)^k) : ℤ) : ℂ)

/-- The literal full existence claim fails already for `k=1`. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨P, hd, he⟩ := h 1 (by norm_num)
  have hp := Polynomial.eq_X_add_C_of_natDegree_le_one (hd 0 (by norm_num)).le
  have h2 := he 2 (by norm_num)
  have h4 := he 4 (by norm_num)
  have h6 := he 6 (by norm_num)
  norm_num [a, numerator] at h2 h4 h6
  rw [hp] at h2 h4 h6
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at h2 h4 h6
  have hc : (1 : ℂ) = 0 := by linear_combination h2 - 2*h4 + h6
  norm_num at hc

#print axioms result
end D5.S3.Arith.Congruence.SelfPowerResiduePolynomialRefutation
