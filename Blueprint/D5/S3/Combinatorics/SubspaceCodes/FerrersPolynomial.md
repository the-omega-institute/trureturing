# Linearized polynomial rank

## Abstract

The root bound for a four-term linearized polynomial gives rank at least nine.

**Definition 1.1 (Linearized evaluation map).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized`

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite field F of order q, an extension E of F, and coefficients a indexed by Fin 4, the F-linear map on E is the sum of the first four iterates of the q-Frobenius, scaled by the corresponding coefficients in E.

**Theorem 1.2 (Evaluation by Frobenius powers).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite field F of order q and an extension field E, evaluation of a coefficient tuple a indexed by Fin 4 at x in E is the sum of aᵢ x^(qⁱ).

**Theorem 1.3 (Rank bound in degree twelve).**

Lean statement: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.finrank_range_evaluateLinearized_ge_nine`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.finrank_range_evaluateLinearized_ge_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a finite extension of degree twelve, the evaluation map of any nonzero coefficient tuple has F-linear rank at least nine. The polynomial has distinct exponents 1, q, q² and q³ and degree at most q³. Its kernel therefore has at most q³ elements and dimension at most three.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.evaluateLinearized_apply`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/FerrersPolynomial.finrank_range_evaluateLinearized_ge_nine`
