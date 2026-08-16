# A Distinct Polynomial Factorization Pair

## Abstract

An explicit polynomial has two distinct nonnegative-coefficient factorizations.

**Theorem 1.1 (The Sicherman polynomial has two distinct factorization pairs).**

$$(1+X)(1+X^{2}+X^{4})=(1+X+X^{2})(1+X^{3}) \land (1+X, 1+X^{2}+X^{4})\neq(1+X+X^{2}, 1+X^{3}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/SichermanFactorization.sicherman_polynomial_has_distinct_factorizations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a clause-level closure of appendix E.146. It formalizes the displayed identity over the natural-coefficient polynomial semiring and proves that the two ordered factor pairs are different.

It does not establish a general failure of unique factorization for natural-coefficient polynomials, classify ambiguous spectra, or formalize the atom's quantum-information interpretation.

Pinned Mathlib was searched before proving. No exact declaration was found. The product identity is closed by commutative-semiring normalization, and distinctness follows because the first factors have different coefficients at degree two.

## References

- Truth anchor: `D5/S3/ArithUnits/SichermanFactorization.sicherman_polynomial_has_distinct_factorizations`
