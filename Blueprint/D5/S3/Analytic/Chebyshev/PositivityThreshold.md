# Positivity of all Chebyshev values at a point

## Abstract

Every Chebyshev value T_n(s) with n ≥ 1 is positive exactly when s ≥ 1.

Let T_n be the Chebyshev polynomial of the first kind of index n, with real coefficients, so that T_0 = 1, T_1 = X and T_(n+2) = 2X T_(n+1) − T_n. For a real number s the values T_1(s), T_2(s), T_3(s), … form a sequence obeying the same three-term recurrence. The question treated here is for which s every term of this sequence is positive.

**Theorem 1.1 (The first index with a negative cosine).**

Lean statement: `D5/S3/Analytic/Chebyshev/PositivityThreshold.cos_floor_succ_mul_neg_and_cos_nonneg_before`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Chebyshev/PositivityThreshold.cos_floor_succ_mul_neg_and_cos_nonneg_before` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 0 < α < π and n₀ = ⌊π/(2α)⌋ + 1, where ⌊·⌋ is the floor of a nonnegative real number. Then cos(n₀α) < 0, and cos(nα) ≥ 0 for every natural number n < n₀. So n₀ is the first natural index at which the sequence cos(nα) becomes negative.

Proof: put x = π/(2α) > 0. The floor satisfies ⌊x⌋ ≤ x < ⌊x⌋ + 1, and xα = π/2. Hence n₀α > π/2, while n₀α ≤ (x + 1)α = π/2 + α < 3π/2, and cosine is negative on the open interval (π/2, 3π/2). For n < n₀ one has n ≤ ⌊x⌋ ≤ x, so 0 ≤ nα ≤ π/2, where cosine is nonnegative. The value n = 0 is included, with cos 0 = 1.

**Theorem 1.2 (All values positive exactly from one on).**

Lean statement: `D5/S3/Analytic/Chebyshev/PositivityThreshold.forall_pos_eval_T_iff_one_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Chebyshev/PositivityThreshold.forall_pos_eval_T_iff_one_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real number s, T_n(s) > 0 holds for every natural number n ≥ 1 if and only if s ≥ 1. The index n = 0 is excluded, since T_0(s) = 1 for every s.

Proof: for s ≥ 1 write s = cosh t with t ≥ 0; then T_n(s) = cosh(nt) ≥ 1 for every n. Conversely, suppose s < 1. If s ≤ −1, already T_1(s) = s is negative. If −1 < s < 1, put α = arccos s, so that 0 < α < π and s = cos α. The identity T_n(cos α) = cos(nα) and the previous theorem give an index n₀ ≥ 1 with T_n₀(s) = cos(n₀α) < 0. In that case n₀ is also the first index n ≥ 1 with T_n(s) < 0, and the terms before it are nonnegative.

The two evaluation identities T_n(cosh t) = cosh(nt) and T_n(cos α) = cos(nα), and the bound T_n(s) ≥ 1 for s ≥ 1, are classical properties of Chebyshev polynomials and are used here as stated in Mathlib. The criterion is a statement about real polynomials only; it asserts nothing about any physical system or interpretation of the sequence.

## References

- Truth anchor: `D5/S3/Analytic/Chebyshev/PositivityThreshold.cos_floor_succ_mul_neg_and_cos_nonneg_before`
- Truth anchor: `D5/S3/Analytic/Chebyshev/PositivityThreshold.forall_pos_eval_T_iff_one_le`
