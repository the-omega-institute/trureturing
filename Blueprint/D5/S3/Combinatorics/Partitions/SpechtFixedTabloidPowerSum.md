# Power sums and fixed tabloids in arbitrary finite alphabets

## Abstract

Power sums and fixed tabloids in arbitrary finite alphabets

This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.

fixedTabloids(n,nu,pi) means Nat.card of the subtype of left cosets q of the actual Young subgroup youngSubgroup nu satisfying pi smul q = q. It is a count of actual tabloids. psumPart is the existing Mathlib product of power sums, one factor per full partition part including one-cycles. The alphabet is finite but its size may be smaller than n. Every partition of n occurs in the monomial expansion; monomials that do not fit the alphabet contribute zero.

The implementation selects the invariant-colouring expansion, the equivariant coset-to-colouring equivalence, sorted exponent coordinates, and coefficient isolation. It omits the independent averaging formula, the full Schur basis, and every unused companion. The displayed class equality is equality of conjugacy classes under the existing full-partition equivalence.

**Theorem 1.1 (Fixed-tabloid monomial expansion).**

$$\forall sigma \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(sigma\right)], \forall R \in \operatorname{Type}*,\; [\operatorname{CommSemiring}\left(R\right)], \forall n \in \operatorname{Nat},\; \forall rho \in \operatorname{Partition}\left(n\right),\; \forall pi \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; (\operatorname{ConjClassesMk}\left(pi\right) = \operatorname{partitionEquivConjClasses}\left(n, rho\right)) \Rightarrow (\operatorname{psumPart}\left(sigma, R, rho\right) = \sum_{nu: \operatorname{Partition}\left(n\right)} (\operatorname{smul}\left(\operatorname{natCast}\left(\operatorname{fixedTabloids}\left(n, nu, pi\right), R\right), \operatorname{msymm}\left(sigma, R, nu\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

Necessary source comparison in the full HSW construction. The displayed abbreviations are defined by the narrative above. There is no independent firstfreeze or standalone admission claim; the remaining public-declaration audit is tracked in issue 24542.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates](SpechtMonomialCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtOrdinaryTrace](SpechtOrdinaryTrace.md)
