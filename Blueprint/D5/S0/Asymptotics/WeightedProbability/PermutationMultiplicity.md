# Full permutation multiplicities

## Abstract

The multiplicity factor of a full permutation partition includes its fixed-point factorial.

**Definition 1.1 (The multiplicity factor).**

$$\forall m \in \operatorname{Multiset}\left(\mathbb{N}\right),\; \operatorname{z}\left(m\right) = \prod_{l\in \operatorname{toFinset}\left(m\right)} l^{\operatorname{count}\left(m, l\right)} \cdot \operatorname{factorial}\left(\operatorname{count}\left(m, l\right)\right)$$

*Formalization.* `D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity.z` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Conjugacy class sizes in the symmetric group*. URL: <https://github.com/TauCetiProject/TauCeti/blob/d7ac608e0c97f71e9e0dc210d26a470d974368d7/TauCeti/RepresentationTheory/Symmetric/ClassSize.lean>.

*Commentary.*

For a multiset m of natural numbers, z(m) is the product of l^(count_m(l)) times count_m(l)! over its distinct entries. This is the Tau Ceti full-partition normalization used in the distinct-cycle-size limit.

**Theorem 1.2 (Extending the finite product).**

$$\forall m \in \operatorname{Multiset}\left(\mathbb{N}\right),\; \forall s \in \operatorname{Finset}\left(\mathbb{N}\right),\; \operatorname{Subset}\left(\operatorname{toFinset}\left(m\right), s\right) \Rightarrow \operatorname{z}\left(m\right) = \prod_{l\in s} l^{\operatorname{count}\left(m, l\right)} \cdot \operatorname{factorial}\left(\operatorname{count}\left(m, l\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity.hz_prod` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Conjugacy class sizes in the symmetric group*. URL: <https://github.com/TauCetiProject/TauCeti/blob/d7ac608e0c97f71e9e0dc210d26a470d974368d7/TauCeti/RepresentationTheory/Symmetric/ClassSize.lean>.

*Commentary.*

Any finite set containing the support gives the same product: missing entries have multiplicity zero and factor one.

**Theorem 1.3 (Cycle type and fixed points).**

$$\forall A \in Type,\; \operatorname{Fintype}\left(A\right) \Rightarrow \left(\operatorname{DecidableEq}\left(A\right) \Rightarrow \left(\forall sigma \in \operatorname{Perm}\left(A\right),\; \operatorname{z}\left(\operatorname{parts}\left(\operatorname{partition}\left(sigma\right)\right)\right) = \operatorname{factorial}\left(\operatorname{tsub}\left(\operatorname{FintypeCard}\left(A\right), \operatorname{sum}\left(\operatorname{cycleType}\left(sigma\right)\right)\right)\right) \cdot \operatorname{prod}\left(\operatorname{cycleType}\left(sigma\right)\right) \cdot \operatorname{MultiplicityFactorialProduct}\left(\operatorname{cycleType}\left(sigma\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity.hz_perm` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Conjugacy class sizes in the symmetric group*. URL: <https://github.com/TauCetiProject/TauCeti/blob/d7ac608e0c97f71e9e0dc210d26a470d974368d7/TauCeti/RepresentationTheory/Symmetric/ClassSize.lean>.

*Commentary.*

For every permutation of a finite carrier A, z(partition(sigma)) equals (card(A)-sum(cycleType(sigma)))! times prod(cycleType(sigma)) times the product of count(l)! over the distinct nontrivial cycle lengths. The omitted singleton cycles are restored by the first factorial. This normalization is adapted from Tau Ceti's symmetric-group partition and class-size development; the complete Apache 2.0 license is retained in the cited note.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity.hz_perm`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity.hz_prod`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity.z`
