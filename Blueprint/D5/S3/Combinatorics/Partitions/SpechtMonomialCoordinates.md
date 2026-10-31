# Sorted coordinates preserve symmetric coefficients

## Abstract

Sorted coordinates preserve symmetric coefficients

This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.

For a finite alphabet sigma, every exponent d of degree n can be permuted to the sorted coordinate partWeight sigma (weightPartition d h). This coordinate records the literal partition of the nonzero exponents, with zero padding to the alphabet size. A symmetric polynomial has the same coefficient at these two exponents. The fixed-tabloid coefficient calculation consumes this permutation result directly. The unused monomial-symmetric expansion branch is omitted.

**Theorem 1.1 (Sorted coordinates preserve symmetric coefficients).**

$$\forall sigma \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(sigma\right)], [\operatorname{DecidableEq}\left(sigma\right)], \forall R \in \operatorname{Type}*,\; [\operatorname{CommSemiring}\left(R\right)], \forall n \in \operatorname{Nat},\; \forall p \in \operatorname{MvPolynomial}\left(sigma, R\right),\; \forall hp \in \operatorname{IsSymmetric}\left(p\right),\; \forall d \in \operatorname{Finsupp}\left(sigma, \operatorname{Nat}\right),\; \forall h \in \operatorname{degree}\left(d\right) = n,\; \operatorname{coeff}\left(p, d\right) = \operatorname{coeff}\left(p, \operatorname{partWeight}\left(sigma, \operatorname{weightPartition}\left(d, h\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates.coeff_eq_coeff_partWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

This coefficient lemma is consumed in the compiled full ordinary-character HSW proof. There is no independent firstfreeze or standalone admission claim; the remaining public-declaration audit is tracked in issue 24542.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates.coeff_eq_coeff_partWeight`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtPolytabloid](SpechtPolytabloid.md)
