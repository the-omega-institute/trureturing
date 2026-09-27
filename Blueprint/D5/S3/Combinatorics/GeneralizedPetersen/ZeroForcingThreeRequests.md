# Requests, Collisions, and Cyclic Gap Scores

## Abstract

The external boundary is counted by requests and collisions, whose total is dominated by ten cyclic layer scores.

**Definition 1.1 (Forward requests).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; 0 < n \Rightarrow \operatorname{positiveRequests}\left(n, X\right) = \left\{\operatorname{positiveShift}\left(n, v\right) \mid v \in X\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positiveRequests` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Each selected vertex requests its forward neighbor in the same layer.

**Definition 1.2 (Backward requests).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; 0 < n \Rightarrow \operatorname{negativeRequests}\left(n, X\right) = \left\{\operatorname{negativeShift}\left(n, v\right) \mid v \in X\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.negativeRequests` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Each selected vertex requests its backward neighbor in the same layer.

**Definition 1.3 (Requests landing in occupied columns).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; 0 < n \Rightarrow \operatorname{I}\left(n, X\right) = \operatorname{card}\left(\operatorname{inter}\left(\operatorname{positiveRequests}\left(n, X\right), \operatorname{occupiedVertices}\left(X\right)\right)\right) + \operatorname{card}\left(\operatorname{inter}\left(\operatorname{negativeRequests}\left(n, X\right), \operatorname{occupiedVertices}\left(X\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.I` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Count requests into occupied columns separately in the two directions, retaining multiplicity when both directions reach the same vertex.

**Definition 1.4 (Two requests at an empty column).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; 0 < n \Rightarrow \operatorname{K}\left(n, X\right) = \operatorname{card}\left(\operatorname{inter}\left((\operatorname{positiveRequests}\left(n, X\right) \setminus \operatorname{occupiedVertices}\left(X\right)), (\operatorname{negativeRequests}\left(n, X\right) \setminus \operatorname{occupiedVertices}\left(X\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A collision is a vertex in an unoccupied column requested from both directions.

**Theorem 1.5 (Boundary, requests, and collisions).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; 14 \le n \Rightarrow \operatorname{card}\left(\operatorname{externalBoundary}\left(n, X\right)\right) + \operatorname{I}\left(n, X\right) + \operatorname{K}\left(n, X\right) = 2 \cdot \operatorname{card}\left(\operatorname{columns}\left(X\right)\right) + \operatorname{card}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.boundary_request_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For every selected set at circumference at least fourteen, the boundary size plus the occupied requests and empty collisions equals twice the number of occupied columns plus the set size.

**Definition 1.6 (Increasing enumeration of the support).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{sortedColumn}\left(C\right) = \operatorname{orderEmbOfFin}\left(C\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.sortedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The support is enumerated in increasing order by Fin of its cardinality.

**Definition 1.7 (The terminal circumference).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall j \in \mathrm{Nat},\; \operatorname{extendedColumn}\left(C, j\right) = \operatorname{if}\left(j < \operatorname{card}\left(C\right), \operatorname{val}\left(\operatorname{sortedColumn}\left(C\right)[j]\right), n\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.extendedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

At an index below the support size, take the corresponding sorted column value; at every later index, take n.

**Definition 1.8 (Positive cyclic differences).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; \operatorname{gapWord}\left(C, i\right) = \operatorname{extendedColumn}\left(C, \operatorname{val}\left(i\right) + 1\right) - \operatorname{extendedColumn}\left(C, \operatorname{val}\left(i\right)\right) + \operatorname{if}\left(\operatorname{val}\left(i\right) + 1 = \operatorname{card}\left(C\right), \operatorname{extendedColumn}\left(C, 0\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.gapWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Consecutive sorted columns give the ordinary gaps; the final entry includes the wrap from the last occupied column to the first.

**Definition 1.9 (One outer-gap contribution).**

$$\forall h \in \mathrm{Nat},\; \operatorname{phi}\left(h\right) = \operatorname{if}\left(h = 1, 2, \operatorname{if}\left(h = 2, 1, 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A gap of one contributes two, a gap of two contributes one, and every other gap contributes zero.

**Definition 1.10 (Cyclic displacement of an index).**

$$\forall c \in \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(c\right),\; \forall j \in \mathrm{Nat},\; \operatorname{val}\left(\operatorname{cyclicIndex}\left(i, j\right)\right) = \left(\operatorname{val}\left(i\right) + j\right) \bmod c$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.cyclicIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Add j to the index and reduce modulo the word length.

**Definition 1.11 (Forward cyclic prefix sum).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(c\right),\; \forall k \in \mathrm{Nat},\; \operatorname{positivePrefix}\left(h, i, k\right) = \sum _{j \in \operatorname{range}\left(k\right)}\operatorname{h}\left(\operatorname{cyclicIndex}\left(i, j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positivePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Sum k gaps starting with the gap at i and proceeding forward.

**Definition 1.12 (Backward cyclic prefix sum).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(c\right),\; \forall k \in \mathrm{Nat},\; \operatorname{negativePrefix}\left(h, i, k\right) = \sum _{j \in \operatorname{range}\left(k\right)}\operatorname{h}\left(\operatorname{cyclicIndex}\left(i, c - \left(j + 1\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.negativePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The reverse scan uses the displacement c - (j + 1). This subtraction is in the natural numbers and is truncated at zero.

**Definition 1.13 (Score of a directional prefix scan).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(c\right),\; \forall sums \in \left(\operatorname{Fin}\left(c\right) \to \mathrm{Nat}\right) \to \left(\operatorname{Fin}\left(c\right) \to \left(\mathrm{Nat} \to \mathrm{Nat}\right)\right),\; \operatorname{prefixScore}\left(h, i, sums\right) = \operatorname{if}\left(\exists k \in \mathrm{Nat},\; 1 \le k \land \left(k \le c \land \operatorname{sums}\left(h, i, k\right) = 3\right), 2, \operatorname{if}\left(\exists k \in \mathrm{Nat},\; 1 \le k \land \left(k \le c \land \operatorname{sums}\left(h, i, k\right) = 6\right), 1, 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.prefixScore` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A prefix of one through c gaps summing to three scores two. If none exists, a prefix summing to six scores one; otherwise the score is zero.

**Definition 1.14 (The outer layer slot).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(c\right),\; \operatorname{A}\left(h, i\right) = \operatorname{phi}\left(\operatorname{h}\left(\operatorname{cyclicIndex}\left(i, c - 1\right)\right)\right) + \operatorname{phi}\left(\operatorname{h}\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The outer slot adds the contributions from the gaps immediately before and after its column.

**Definition 1.15 (The inner layer slot).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall i \in \operatorname{Fin}\left(c\right),\; \operatorname{B}\left(h, i\right) = \operatorname{prefixScore}\left(h, i, \mathrm{positivePrefix}\right) + \operatorname{prefixScore}\left(h, i, \mathrm{negativePrefix}\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The inner slot adds the two directional prefix scores.

**Definition 1.16 (The supremum of ten selected slots).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \operatorname{T}\left(h\right) = \operatorname{sup}\left(\operatorname{powersetCard}\left(\operatorname{univ}\left(\mathrm{Bool}\times \operatorname{Fin}\left(c\right)\right), 10\right), (\lambda Y:\operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(c\right)\right), \sum _{v \in Y}\operatorname{if}\left(\operatorname{fst}\left(v\right) = \mathrm{true}, \operatorname{B}\left(h, \operatorname{snd}\left(v\right)\right), \operatorname{A}\left(h, \operatorname{snd}\left(v\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Take the supremum of the sums over all sets of ten layer-column slots. When fewer than ten slots exist, the family is empty and the natural-number supremum is zero.

**Definition 1.17 (Unwrapped support coordinates).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; \forall k \in \mathrm{Nat},\; \operatorname{liftedColumn}\left(C, i, k\right) = \operatorname{if}\left(\operatorname{val}\left(i\right) + k < \operatorname{card}\left(C\right), \operatorname{extendedColumn}\left(C, \operatorname{val}\left(i\right) + k\right), n + \operatorname{extendedColumn}\left(C, \operatorname{val}\left(i\right) + k - \operatorname{card}\left(C\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.liftedColumn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The coordinate continues beyond one wrap by adding n after the index reaches the support size.

**Theorem 1.18 (A prefix is an unwrapped displacement).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; \forall k \in \mathrm{Nat},\; k \le \operatorname{card}\left(C\right) \Rightarrow \operatorname{positivePrefix}\left(\operatorname{gapWord}\left(C\right), i, k\right) = \operatorname{liftedColumn}\left(C, i, k\right) - \operatorname{liftedColumn}\left(C, i, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positivePrefix_lifted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A prefix of at most one full cycle equals the difference of the corresponding lifted support coordinates.

**Theorem 1.19 (An occupied endpoint determines a prefix).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; \forall d \in \mathrm{Nat},\; \left(0 < n \land \left(0 < d \land \left(d < n \land \operatorname{sortedColumn}\left(C, i\right) + \operatorname{ofNat}\left(n, d\right) \in C\right)\right)\right) \Rightarrow \left(\exists k \in \mathrm{Nat},\; 1 \le k \land \left(k \le \operatorname{card}\left(C\right) \land \operatorname{positivePrefix}\left(\operatorname{gapWord}\left(C\right), i, k\right) = d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positive_request_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

If a positive displacement less than n reaches another occupied column, that displacement is the sum of a nonempty cyclic gap prefix.

**Theorem 1.20 (A short prefix determines its endpoint).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; \forall k \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \left(0 < n \land \left(1 \le k \land \left(k \le \operatorname{card}\left(C\right) \land \left(d < n \land \operatorname{positivePrefix}\left(\operatorname{gapWord}\left(C\right), i, k\right) = d\right)\right)\right)\right) \Rightarrow \operatorname{sortedColumn}\left(C, \operatorname{cyclicIndex}\left(i, k\right)\right) = \operatorname{sortedColumn}\left(C, i\right) + \operatorname{ofNat}\left(n, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positivePrefix_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A nonempty prefix of at most one cycle, with total below n, ends at the column obtained by adding that total modulo n.

**Theorem 1.21 (Ten slots dominate requests and collisions).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \left(14 \le n \land \operatorname{card}\left(X\right) = 10\right) \Rightarrow 2 \cdot \left(\operatorname{I}\left(n, X\right) + \operatorname{K}\left(n, X\right)\right) \le \operatorname{T}\left(\operatorname{gapWord}\left(\operatorname{columns}\left(X\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.slot_domination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For a ten-vertex set at circumference at least fourteen, twice the sum of occupied requests and empty collisions is at most the ten-slot score of its gap word.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.A`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.B`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.I`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.K`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.T`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.boundary_request_identity`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.cyclicIndex`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.extendedColumn`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.gapWord`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.liftedColumn`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.negativePrefix`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.negativeRequests`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.phi`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positivePrefix`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positivePrefix_endpoint`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positivePrefix_lifted`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positiveRequests`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.positive_request_prefix`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.prefixScore`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.slot_domination`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.sortedColumn`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary](ZeroForcingThreeBoundary.md)
