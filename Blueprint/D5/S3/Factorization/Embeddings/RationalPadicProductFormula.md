# The Rational p-adic Product Formula

## Abstract

The usual rational norm and all prime-indexed p-adic norms satisfy the product formula.

**Theorem 1.1 (Only finitely many p-adic factors are nontrivial).**

$$\forall x \in \mathbb{Q}, x \neq 0 \Rightarrow \operatorname{Finite}(\{p \in Nat.Primes \mid \left|x\right|_p \neq 1\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalPadicProductFormula.rational_padic_norm_hasFiniteMulSupport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero rational, every prime outside the numerator and denominator factorization supports has p-adic norm one. Thus the all-primes product is algebraically finite and needs no convergence premise.

**Theorem 1.2 (The rational archimedean and p-adic norms multiply to one).**

$$\forall x \in \mathbb{Q}, x \neq 0 \Rightarrow \left|x\right|_\infty \prod^{\operatorname{fin}}_{p \in Nat.Primes} \left|x\right|_p = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/RationalPadicProductFormula.rational_padic_product_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write a nonzero rational as its reduced integer numerator divided by its positive natural denominator. Prime factorization shows that the finite product of p-adic norms of each nonzero natural number is its reciprocal.

The p-adic norm ignores the sign of the numerator and respects division. The numerator and denominator factors therefore cancel the usual absolute value exactly, leaving one.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/RationalPadicProductFormula.rational_padic_norm_hasFiniteMulSupport`
- Truth anchor: `D5/S3/Factorization/Embeddings/RationalPadicProductFormula.rational_padic_product_formula`
- Dependency: [D5/S3/Factorization/Embeddings/RationalValuationRecovery](RationalValuationRecovery.md)
