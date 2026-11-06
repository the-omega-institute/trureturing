/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff, mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: The affine polynomial pair has Werner's conjectured binomial coefficients. -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
open Polynomial
noncomputable section

/-- The source polynomial pair, with stage zero representing source index one. -/
def pair : ℕ → Polynomial ℤ × Polynomial ℤ
  | 0 => (1, 1)
  | m + 1 => ((pair m).1 + X * (pair m).2,
      (pair m).1 + (pair m).2 + 1)

/-- Knud Werner's all-column conjecture for the second polynomial of OEIS A208509. -/
theorem werner_a208509 : ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
    ((pair (n - 1)).2).coeff k =
      (Nat.choose (n - 1) (2*k+1) : ℤ) + (Nat.choose n (2*k+1) : ℤ) := by
  have inv : ∀ m k : ℕ,
      ((pair m).1).coeff k =
        (Nat.choose m (2*k) : ℤ) + (Nat.choose (m+1) (2*k) : ℤ) -
          (if k = 0 then 1 else 0) ∧
      ((pair m).2).coeff k =
        (Nat.choose m (2*k+1) : ℤ) + (Nat.choose (m+1) (2*k+1) : ℤ) := by
    intro m
    induction m with
    | zero =>
      intro k
      cases k with
      | zero => norm_num [pair]
      | succ k =>
        have h0 : 0 < 2*(k+1) := by omega
        have h1 : 1 < 2*(k+1) := by omega
        have h2 : 0 < 2*(k+1)+1 := by omega
        have h3 : 1 < 2*(k+1)+1 := by omega
        simp [pair, coeff_one, Nat.choose_eq_zero_of_lt h0, Nat.choose_eq_zero_of_lt h1,
          Nat.choose_eq_zero_of_lt h2, Nat.choose_eq_zero_of_lt h3]
    | succ m ih =>
      intro k
      constructor
      · cases k with
        | zero => simpa [pair, Nat.choose_zero_right] using (ih 0).1
        | succ k =>
          simp only [pair, coeff_add, coeff_X_mul]
          rw [(ih (k+1)).1, (ih k).2]
          simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
            sub_zero]
          have h : 2*(k+1) = (2*k+1)+1 := by omega
          rw [h]
          simp only [Nat.choose_succ_succ', Nat.cast_add]
          ring
      · simp only [pair, coeff_add]
        rw [(ih k).1, (ih k).2]
        have hc : (1 : Polynomial ℤ).coeff k = if k = 0 then 1 else 0 := by
          simp [coeff_one]
        rw [hc]
        simp only [Nat.choose_succ_succ', Nat.cast_add]
        ring
  intro n hn k
  have h := (inv (n-1) k).2
  have he : n-1+1 = n := by omega
  simpa only [he] using h

#print axioms werner_a208509

end
end D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
