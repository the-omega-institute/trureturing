# Uniqueness of the Squarefree-Square Decomposition

## Abstract

The squarefree-times-square factorization of a positive integer is unique.

**Theorem 1.1 (The squarefree-times-square factorization is unique).**

$$\operatorname{Squarefree} a_1, \operatorname{Squarefree} a_2, b_1 \neq 0, b_1^{2}a_1 = b_2^{2}a_2\\\Rightarrow a_1 = a_2 \land b_1 = b_2$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/SquarefreeSquareDecomposition.bcs_square_squarefree_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive integer's factorization as a squarefree number times a perfect square is unique. If b1^2 * a1 = b2^2 * a2 with a1 and a2 squarefree and b1 not zero, then the squarefree parts agree (a1 = a2) and the square roots agree (b1 = b2). The hypothesis b1 not zero (equivalently n not zero) is essential: n = 0 leaves the squarefree part unconstrained.

The proof is prime by prime. The p-adic valuation of n = b^2 * a is v_p(n) = 2 v_p(b) + v_p(a), and squarefreeness bounds v_p(a) <= 1. Two values in {0,1} that leave the same residue modulo 2 (as forced by the common v_p(n)) are equal, so v_p(a1) = v_p(a2) at every prime; hence a1 = a2 by equality of factorizations. Cancelling the common squarefree part gives b1^2 = b2^2, and squaring is injective on the naturals, so b1 = b2.

Mathlib supplies only the existence of the squarefree-times-square decomposition (Nat.sq_mul_squarefree), not the uniqueness recorded here, so this is a genuine addition. It is the uniqueness half of the BCS decomposition, part P1 of the source's three-part arithmetic-statistics theorem; the existence half, the k-free ladder (P2), and the Mobius / reciprocal-zeta identity (P3) are not covered.

## References

- Truth anchor: `D5/S3/Factorization/SquarefreeSquareDecomposition.bcs_square_squarefree_unique`
