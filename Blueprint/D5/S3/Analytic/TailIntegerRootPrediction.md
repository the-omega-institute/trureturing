# Exact Integer Roots of Two Golden Tail Rows

## Abstract

The row-eight and row-ten tail polynomials have exactly the predicted integer roots.

**Theorem 1.1 (The two predicted tail roots are unique).**

$$(\forall b \in \mathbb{N},\ T_{8}(b) = 0 \Leftrightarrow b = 83) \land (\forall b \in \mathbb{N},\ T_{10}(b) = 0 \Leftrightarrow b = 41).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/TailIntegerRootPrediction.tail_integer_roots_are_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a row with only its first two principal parts present, the tail specializes to P1 times choose(b,0) plus P2 times choose(b+1,1). The displayed row-eight values P1 = 42 and P2 = -1/2 therefore give a zero exactly at b = 83. The row-ten values P1 = 336 and P2 = -8 give a zero exactly at b = 41.

The proof uses Mathlib's Nat.choose_zero_right and Nat.choose_one_right to reduce both binomial-basis expressions to affine rational equations. Exact cast transport and linear arithmetic prove both directions, so the two displayed values are roots and no other natural-number arguments are roots.

This theorem formalizes only the source atom's two tail-polynomial root predictions. It does not assert the separate bridge from a tail root to an e-table coefficient, the all-order principal-part formula, the finite-part cancellations, or the empirical onset law.

Repository, digestion, digest, git-history, generalized theorem-shape, and in-flight searches found no existing declaration for either root. The escape witness is the public equivalence itself: the two source-specific rational cancellations compute new exact and unique natural roots rather than projecting a frozen theorem.

## References

- Truth anchor: `D5/S3/Analytic/TailIntegerRootPrediction.tail_integer_roots_are_exact`
