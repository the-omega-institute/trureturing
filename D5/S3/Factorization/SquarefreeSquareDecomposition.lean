/- GID: D5/S3/Factorization/SquarefreeSquareDecomposition
   generality: G
   mirror-B: D5/B/S3/Factorization/SquarefreeSquareDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every positive integer has a unique squarefree-times-square factorization: if b₁²·a₁ = b₂²·a₂ with a₁, a₂ squarefree and b₁ ≠ 0, then a₁ = a₂ and b₁ = b₂. Prime by prime, the p-adic valuation is 2·v_p(b) + v_p(a) with v_p(a) ≤ 1 (squarefree), which fixes the parity so the squarefree parts agree and the square roots follow. This is the uniqueness half of the BCS decomposition (residual §6.49 part P1); the existence half, the k-free ladder (P2), and the Möbius/reciprocal-zeta identity (P3) are not covered. -/

import Mathlib

open Nat

namespace D5.S3.Factorization.SquarefreeSquareDecomposition

/-- **BCS decomposition uniqueness (§6.49, P1).** The representation `n = b² · a` with `a`
squarefree is unique: both the squarefree part `a` and the square-root part `b` are determined.
The hypothesis `b₁ ≠ 0` (equivalently `n ≠ 0`) is essential — without it `n = 0` leaves the
squarefree parts unconstrained. Only the uniqueness half is recorded here; the existence half
(Mathlib's `Nat.sq_mul_squarefree`), the k-free ladder, and the Möbius/reciprocal-zeta identity of
the source are not covered. -/
theorem bcs_square_squarefree_unique
    {a₁ b₁ a₂ b₂ : ℕ} (hb₁ : b₁ ≠ 0)
    (ha₁ : Squarefree a₁) (ha₂ : Squarefree a₂)
    (h : b₁ ^ 2 * a₁ = b₂ ^ 2 * a₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have ha₁0 : a₁ ≠ 0 := ha₁.ne_zero
  have ha₂0 : a₂ ≠ 0 := ha₂.ne_zero
  have hb₁2 : b₁ ^ 2 ≠ 0 := pow_ne_zero 2 hb₁
  have hn0 : b₁ ^ 2 * a₁ ≠ 0 := mul_ne_zero hb₁2 ha₁0
  have hb₂2 : b₂ ^ 2 ≠ 0 := by
    intro hz; apply hn0; rw [h, hz, zero_mul]
  -- factorization agrees prime-by-prime on the squarefree parts
  have key : ∀ p, a₁.factorization p = a₂.factorization p := by
    intro p
    have e1 : (b₁ ^ 2 * a₁).factorization p
        = 2 * b₁.factorization p + a₁.factorization p := by
      rw [Nat.factorization_mul hb₁2 ha₁0, Nat.factorization_pow, Finsupp.add_apply,
          Finsupp.smul_apply, smul_eq_mul]
    have e2 : (b₂ ^ 2 * a₂).factorization p
        = 2 * b₂.factorization p + a₂.factorization p := by
      rw [Nat.factorization_mul hb₂2 ha₂0, Nat.factorization_pow, Finsupp.add_apply,
          Finsupp.smul_apply, smul_eq_mul]
    have hr1 : a₁.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one ha₁0).1 ha₁ p
    have hr2 : a₂.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one ha₂0).1 ha₂ p
    have hh : (b₁ ^ 2 * a₁).factorization p = (b₂ ^ 2 * a₂).factorization p := by rw [h]
    rw [e1, e2] at hh
    omega
  have haeq : a₁ = a₂ := Nat.eq_of_factorization_eq ha₁0 ha₂0 key
  refine ⟨haeq, ?_⟩
  rw [← haeq] at h
  have hbsq : b₁ ^ 2 = b₂ ^ 2 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha₁0) h
  exact Nat.pow_left_injective (by norm_num) hbsq

end D5.S3.Factorization.SquarefreeSquareDecomposition
