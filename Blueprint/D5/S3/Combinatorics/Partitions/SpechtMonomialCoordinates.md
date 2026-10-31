# Sorted monomial coordinates for the Frobenius comparison

## Abstract

Sorted monomial coordinates for the Frobenius comparison

This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.

For any finite alphabet sigma, a degree-n exponent d determines the literal partition of its nonzero exponents. The sorted coordinate partWeight records the row lengths of YoungDiagram.ofPartition, with zero padding. The monomial symmetric coefficient is one precisely at that exponent partition. These selected helpers are consumed by SpechtFixedTabloidPowerSum; no semistandard-tableau or Schur polynomial has been introduced by this coordinate definition.

**Theorem 1.1 (Monomial symmetric coefficients).**

$$\forall sigma \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(sigma\right)], [\operatorname{DecidableEq}\left(sigma\right)], \forall R \in \operatorname{Type}*,\; [\operatorname{CommSemiring}\left(R\right)], \forall n \in \operatorname{Nat},\; \forall nu \in \operatorname{Partition}\left(n\right),\; \forall d \in \operatorname{Finsupp}\left(sigma, \operatorname{Nat}\right),\; \forall h \in \operatorname{degree}\left(d\right) = n,\; \operatorname{coeff}\left(\operatorname{msymm}\left(sigma, R, nu\right), d\right) = \operatorname{ifThenElse}\left(\operatorname{weightPartition}\left(d, h\right) = nu, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates.coeff_msymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Necessary source comparison in the full HSW construction. The displayed abbreviations are defined by the narrative above. There is no independent firstfreeze or standalone admission claim; the remaining public-declaration audit is tracked in issue 24542.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates.coeff_msymm`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtPolytabloid](SpechtPolytabloid.md)
