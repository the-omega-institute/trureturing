# Power-sum coefficients count actual fixed tabloids

## Abstract

Power-sum coefficients count actual fixed tabloids

This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.

For every finite alphabet sigma and every degree-n exponent d, the coefficient of the full-cycle product psumPart sigma R rho is the count of fixed cosets of the actual Young subgroup of weightPartition d h. Equality of conjugacy classes identifies rho with the full cycle partition of pi, including one-cycles. The coefficient count is cast from the natural numbers into the commutative semiring R. The alphabet size is unrestricted. The invariant-colouring expansion and the equivariant coset-to-colouring equivalence prove this coefficient identity; the full HSW mixed pairing consumes it directly. The unused full monomial-symmetric expansion is omitted.

**Theorem 1.1 (Power-sum coefficients count actual fixed tabloids).**

$$\forall sigma \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(sigma\right)], \forall R \in \operatorname{Type}*,\; [\operatorname{CommSemiring}\left(R\right)], \forall n \in \operatorname{Nat},\; \forall rho \in \operatorname{Partition}\left(n\right),\; \forall pi \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \forall hpi \in \operatorname{ConjClassesMk}\left(pi\right) = \operatorname{partitionEquivConjClasses}\left(n, rho\right),\; \forall d \in \operatorname{Finsupp}\left(sigma, \operatorname{Nat}\right),\; \forall h \in \operatorname{degree}\left(d\right) = n,\; \operatorname{coeff}\left(\operatorname{psumPart}\left(sigma, R, rho\right), d\right) = \operatorname{natCast}\left(\operatorname{fixedTabloids}\left(n, \operatorname{weightPartition}\left(d, h\right), pi\right), R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

This coefficient lemma is consumed in the compiled full ordinary-character HSW proof. There is no independent firstfreeze or standalone admission claim; the remaining public-declaration audit is tracked in issue 24542.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates](SpechtMonomialCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtOrdinaryTrace](SpechtOrdinaryTrace.md)
