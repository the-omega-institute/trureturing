# Explicit Permutation Statistics

## Abstract

Three explicit row orders realize the low targets and the odd midpoint of the ascent spectrum.

**Definition 1.1 (Two-target entries).**

$$\forall n \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \operatorname{twoVal}\left(n, i\right) = \operatorname{if}\left(i = 0, 1, \operatorname{if}\left(i = 1, 0, \operatorname{if}\left(i \le n - 3, n - 1 - i, \operatorname{if}\left(i = n - 2, n - 1, n - 2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianPermutations.twoVal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The two-target order is given entry by entry by its initial swap, descending middle block, and final two values.

**Definition 1.2 (Two-target permutation).**

$$\forall n \in \mathrm{Nat},\; 5 \le n \Rightarrow \operatorname{IsPermutation}\left(\operatorname{twoPermutation}\left(n, n, h\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianPermutations.twoPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For n at least five, the two-target entries form a permutation of Fin n.

**Definition 1.3 (Low-target entries).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \operatorname{lowVal}\left(n, k, i\right) = \operatorname{if}\left(i = 0, k - 1, \operatorname{if}\left(i < k, i - 1, \operatorname{if}\left(i < n - \left(k + 1\right), n - 2 - i, 2 \cdot n - k - \left(2 + i\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianPermutations.lowVal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The low-target order is the concatenation of an initial singleton, an increasing block, a descending block, and a final descending block.

**Definition 1.4 (Low-target permutation).**

$$\forall n \in \mathrm{Nat},\; \left(3 \le k \land 2 \cdot k + 2 \le n\right) \Rightarrow \operatorname{IsPermutation}\left(\operatorname{lowPermutation}\left(n, n, k, h, hn\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianPermutations.lowPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

When k is at least three and 2 k plus 2 is at most n, the low-target entries form a permutation of Fin n.

**Definition 1.5 (Odd-midpoint entries).**

$$\forall m \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \operatorname{midpointVal}\left(m, i\right) = \operatorname{if}\left(i = 0, 0, \operatorname{if}\left(i < m, i + 1, \operatorname{if}\left(i < 2 \cdot m, 3 \cdot m - i, 1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianPermutations.midpointVal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The odd-midpoint order starts with zero, rises through the lower half, descends through the upper half, and ends at one.

**Definition 1.6 (Odd-midpoint permutation).**

$$\forall n \in \mathrm{Nat},\; 2 \le k \Rightarrow \operatorname{IsPermutation}\left(\operatorname{midpointPermutation}\left(n, k, h\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/LatinEulerianPermutations.midpointPermutation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

For m at least two, the odd-midpoint entries form a permutation of Fin (2 m plus 1).

**Theorem 1.7 (Statistics for target two).**

$$\forall n \in \mathrm{Nat},\; \left(5 \le n \land 0 < n\right) \Rightarrow \left(\forall h \in \operatorname{Prop}\left(\right),\; \forall hp \in \operatorname{Prop}\left(\right),\; \operatorname{ordinaryAscents}\left(hp, \operatorname{twoPermutation}\left(n, h\right)\right) = 2 \land \left(\operatorname{forwardUnits}\left(hp, \operatorname{twoPermutation}\left(n, h\right)\right) = 0 \land \left(\operatorname{backwardUnits}\left(hp, \operatorname{twoPermutation}\left(n, h\right)\right) = n - 3 \land \left(\operatorname{val}\left(\operatorname{rowAt}\left(hp, \operatorname{twoPermutation}\left(n, h\right), 0\right)\right) = 1 \land \operatorname{val}\left(\operatorname{rowAt}\left(hp, \operatorname{twoPermutation}\left(n, h\right), n - 1\right)\right) = n - 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianPermutations.two_statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The two-target order has two ordinary ascents, no forward unit steps, n minus three backward unit steps, and endpoint values one and n minus two.

**Theorem 1.8 (Statistics for low targets).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall hk \in \operatorname{Prop}\left(\right),\; \forall hn \in \operatorname{Prop}\left(\right),\; \forall hp \in \operatorname{Prop}\left(\right),\; \left(\left(3 \le k \land 2 \cdot k + 2 \le n\right) \land 0 < n\right) \Rightarrow \left(\operatorname{ordinaryAscents}\left(hp, \operatorname{lowPermutation}\left(n, k, hk, hn\right)\right) = k \land \left(\operatorname{forwardUnits}\left(hp, \operatorname{lowPermutation}\left(n, k, hk, hn\right)\right) = k - 2 \land \left(\operatorname{backwardUnits}\left(hp, \operatorname{lowPermutation}\left(n, k, hk, hn\right)\right) = n - k - 2 \land \left(\operatorname{val}\left(\operatorname{rowAt}\left(hp, \operatorname{lowPermutation}\left(n, k, hk, hn\right), 0\right)\right) = k - 1 \land \operatorname{val}\left(\operatorname{rowAt}\left(hp, \operatorname{lowPermutation}\left(n, k, hk, hn\right), n - 1\right)\right) = n - k - 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianPermutations.low_statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The low-target order has k ordinary ascents, k minus two forward unit steps, n minus k minus two backward unit steps, and the stated endpoint values.

**Theorem 1.9 (Statistics at the odd midpoint).**

$$\forall m \in \mathrm{Nat},\; \forall hm \in \operatorname{Prop}\left(\right),\; \forall hp \in \operatorname{Prop}\left(\right),\; \left(2 \le m \land 0 < 2 \cdot m + 1\right) \Rightarrow \left(\operatorname{ordinaryAscents}\left(hp, \operatorname{midpointPermutation}\left(m, hm\right)\right) = m \land \left(\operatorname{forwardUnits}\left(hp, \operatorname{midpointPermutation}\left(m, hm\right)\right) = m - 2 \land \left(\operatorname{backwardUnits}\left(hp, \operatorname{midpointPermutation}\left(m, hm\right)\right) = m - 1 \land \left(\operatorname{val}\left(\operatorname{rowAt}\left(hp, \operatorname{midpointPermutation}\left(m, hm\right), 0\right)\right) = 0 \land \operatorname{val}\left(\operatorname{rowAt}\left(hp, \operatorname{midpointPermutation}\left(m, hm\right), 2 \cdot m\right)\right) = 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinEulerianPermutations.midpoint_statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Madjid Mirzavaziri, Daniel Yaqubi (2026). *Latin Eulerian Numbers*. DOI: [10.48550/arXiv.2609.25100](https://doi.org/10.48550/arXiv.2609.25100). URL: <https://arxiv.org/abs/2609.25100v1>.

*Commentary.*

The odd-midpoint order has m ordinary ascents, m minus two forward unit steps, m minus one backward unit steps, and endpoint values zero and one.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.lowPermutation`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.lowVal`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.low_statistics`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.midpointPermutation`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.midpointVal`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.midpoint_statistics`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.twoPermutation`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.twoVal`
- Truth anchor: `D5/S3/Combinatorics/LatinEulerianPermutations.two_statistics`
- Dependency: [D5/S3/Combinatorics/LatinEulerianFormula](LatinEulerianFormula.md)
