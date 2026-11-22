# Single-coordinate budgets on the Boolean lattice

## Abstract

Characterize single-coordinate fixed-seed budgets by subset inclusion and parity.

**Theorem 1.1 (A Boolean lattice factor for a single-coordinate budget).**

$$(\operatorname{Even}\left(n + 2\right) \land \operatorname{Odd}\left(k\right)) \Rightarrow (\operatorname{SeedCountsOnAxisWithin}\left(n, k, i, b\right) \Leftrightarrow \operatorname{AxisFactorWithin}\left(n, k, i, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor.axis_budget_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The seed side in dimension n plus two requires zero fixed seeds outside the specified coordinate i and at most b on that coordinate. Both marginals are uniform on their opposite-parity slices.

The graph side uses two copies of the subsets of all coordinates except i. Denote the full subset by T. An edge from A to B is allowed when A is contained in B or A equals T. The edge from T to T is excluded. Choose either even degrees at most k minus one at both copies of T, or odd degrees at most k minus two there with k at least three. Other vertices have odd degree at most k.

The score is four times the sum of one and the number of chosen edges from an odd subset other than T to an odd subset. Its upper bound is b.

Zero counts outside i force the mark to be the singleton of i and every ordinary selected profile pair to intersect only within that singleton. Delete i from the row profile and from the complement of the column profile. The parities recover the deleted bits, and the zero-count constraint becomes subset inclusion. The two marked endpoints both become T.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor.axis_budget_iff`
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParitySeedFactor](ParitySeedFactor.md)
