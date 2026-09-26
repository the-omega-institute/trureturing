# Bounds for Partial Cyclic Gap Words

## Abstract

Short-prefix masks and dual prices bound the ten largest layer scores of every bounded completion.

**Definition 1.1 (Allowed values of an unfinished gap).**

$$\forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall j \in \mathrm{Nat},\; \operatorname{choices}\left(m, p, j\right) = \operatorname{if}\left(j < \operatorname{length}\left(p\right), [p[j]], \operatorname{map}\left((\lambda k:\mathrm{Nat}, k + 1), \operatorname{range}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.choices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

An already specified gap has its single fixed value. Every later gap may take any value from one through m.

**Definition 1.2 (Forward cyclic position).**

$$\forall c \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \operatorname{forward}\left(c, i, j\right) = \left(i + j\right) \bmod c$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.forward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Advance j positions around a cycle of length c.

**Definition 1.3 (Backward cyclic position).**

$$\forall c \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \operatorname{backward}\left(c, i, j\right) = \left(i + c - \left(j + 1\right)\right) \bmod c$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.backward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The reverse scan starts at the gap immediately before i. Natural-number subtraction is truncated at zero.

**Definition 1.4 (Largest possible outer-gap score).**

$$\forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall j \in \mathrm{Nat},\; \operatorname{phiUpper}\left(m, p, j\right) = \operatorname{if}\left(1 \in \operatorname{choices}\left(m, p, j\right), 2, \operatorname{if}\left(2 \in \operatorname{choices}\left(m, p, j\right), 1, 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.phiUpper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A possible gap of one contributes two; otherwise a possible gap of two contributes one; all larger gaps contribute zero.

**Definition 1.5 (Upper bound for an outer slot).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall i \in \mathrm{Nat},\; \operatorname{outer}\left(c, m, p, i\right) = \operatorname{phiUpper}\left(m, p, \operatorname{backward}\left(c, i, 0\right)\right) + \operatorname{phiUpper}\left(m, p, i\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.outer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The outer slot is bounded by the sum of the preceding and following gap bounds.

**Definition 1.6 (A dual price for ten slots).**

$$\forall scores \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall price \in \mathrm{Nat},\; \operatorname{priceBound}\left(scores, price\right) = 10 \cdot price + \operatorname{sum}\left(\operatorname{map}\left((\lambda s:\mathrm{Nat}, s - price), scores\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.priceBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Charge a common price to ten selected slots and add every positive excess above that price. Each subtraction in the natural numbers is truncated at zero.

**Definition 1.7 (The six exceptional rooted words).**

$$\mathrm{exceptionalRoots} = [[6, 2, 1, 2, 1, 2], [3, 2, 1, 2, 1, 2, 3], [3, 3, 2, 1, 2, 1, 2], [6, 2, 1, 1, 1, 1, 2], [3, 2, 1, 1, 1, 1, 2, 3], [3, 3, 2, 1, 1, 1, 1, 2]]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.exceptionalRoots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

These six positive gap lists are the exceptional leaves of the bounded recurrence.

**Definition 1.8 (Reachable short prefix sums).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall i \in \mathrm{Nat},\; \forall reverse \in \mathrm{Bool},\; \operatorname{reachMask}\left(c, m, p, i, reverse, 0\right) = 1 \land \left(\forall k \in \mathrm{Nat},\; \operatorname{reachMask}\left(c, m, p, i, reverse, k + 1\right) = \operatorname{foldl}\left((\lambda mask:\mathrm{Nat}, (\lambda x:\mathrm{Nat}, \operatorname{bitwise}\left(\mathrm{or}, mask, \operatorname{reachMask}\left(c, m, p, i, reverse, k\right) \cdot 2^{x}\right))), 0, \operatorname{choices}\left(m, p, \operatorname{if}\left(reverse = \mathrm{true}, \operatorname{backward}\left(c, i, k\right), \operatorname{forward}\left(c, i, k\right)\right)\right)\right) \bmod 128\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.reachMask` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Bit zero initially represents the empty sum. Each step shifts the preceding mask by every allowed gap and takes their bitwise union, retaining bits zero through six.

**Definition 1.9 (A reachable target distance).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall i \in \mathrm{Nat},\; \forall reverse \in \mathrm{Bool},\; \forall d \in \mathrm{Nat},\; \operatorname{maskHit}\left(c, m, p, i, reverse, d\right) = \mathrm{true} \Leftrightarrow \left(\exists j \in \mathrm{Nat},\; j < c \land \operatorname{testBit}\left(\operatorname{reachMask}\left(c, m, p, i, reverse, j + 1\right), d\right) = \mathrm{true}\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskHit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A target distance is hit if its bit occurs after one through c prefix steps.

**Definition 1.10 (One directional inner score).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall i \in \mathrm{Nat},\; \forall reverse \in \mathrm{Bool},\; \operatorname{maskDirection}\left(c, m, p, i, reverse\right) = \operatorname{if}\left(\operatorname{maskHit}\left(c, m, p, i, reverse, 3\right) = \mathrm{true}, 2, \operatorname{if}\left(\operatorname{maskHit}\left(c, m, p, i, reverse, 6\right) = \mathrm{true}, 1, 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskDirection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A possible prefix of length three scores two. In its absence, a possible prefix of length six scores one.

**Definition 1.11 (Upper bound for an inner slot).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall i \in \mathrm{Nat},\; \operatorname{maskInner}\left(c, m, p, i\right) = \operatorname{maskDirection}\left(c, m, p, i, \mathrm{false}\right) + \operatorname{maskDirection}\left(c, m, p, i, \mathrm{true}\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskInner` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Add the forward and backward inner-direction bounds.

**Definition 1.12 (The list of outer and inner bounds).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{maskSlots}\left(c, m, p\right) = \operatorname{flatten}\left(\operatorname{ofFn}\left((\lambda i:\operatorname{Fin}\left(c\right), [\operatorname{outer}\left(c, m, p, \operatorname{val}\left(i\right)\right), \operatorname{maskInner}\left(c, m, p, \operatorname{val}\left(i\right)\right)])\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskSlots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

At each cyclic index, list the outer bound followed by the inner bound, giving twice c entries.

**Definition 1.13 (The best of five dual prices).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{maskUpper}\left(c, m, p\right) = \operatorname{min}\left(\operatorname{priceBound}\left(\operatorname{maskSlots}\left(c, m, p\right), 0\right), \operatorname{min}\left(\operatorname{priceBound}\left(\operatorname{maskSlots}\left(c, m, p\right), 1\right), \operatorname{min}\left(\operatorname{priceBound}\left(\operatorname{maskSlots}\left(c, m, p\right), 2\right), \operatorname{min}\left(\operatorname{priceBound}\left(\operatorname{maskSlots}\left(c, m, p\right), 3\right), \operatorname{priceBound}\left(\operatorname{maskSlots}\left(c, m, p\right), 4\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskUpper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Take the minimum of priceBound at the five prices zero through four.

**Definition 1.14 (The bounded-completion recurrence).**

$$\forall c \in \mathrm{Nat},\; \forall fuel \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{maskCheck}\left(c, fuel, m, p\right) = \mathrm{true} \Leftrightarrow \left(\operatorname{maskUpper}\left(c, m, p\right) \le 4 \cdot c + 5 \lor \left(4 \cdot c + 5 < \operatorname{maskUpper}\left(c, m, p\right) \land \left(\left(fuel = 0 \land \left(\operatorname{sum}\left(p\right) < 14 \lor p \in \mathrm{exceptionalRoots}\right)\right) \lor \left(0 < fuel \land \left(\forall j \in \mathrm{Nat},\; j < m \Rightarrow \operatorname{maskCheck}\left(c, fuel - 1, m, \operatorname{append}\left(p, [j + 1]\right)\right) = \mathrm{true}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A prefix is accepted when its upper score is at most four times c plus five. Otherwise the recurrence checks every next gap; a leaf must have sum below fourteen or belong to exceptionalRoots.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.backward`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.choices`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.exceptionalRoots`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.forward`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskCheck`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskDirection`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskHit`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskInner`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskSlots`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.maskUpper`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.outer`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.phiUpper`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.priceBound`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute.reachMask`
