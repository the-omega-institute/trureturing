# From Exceptional Gap Words to Layer Supports

## Abstract

Gap prefixes recover the support, and the six exceptional roots reduce to four fourteen-column supports up to reflection.

**Theorem 1.1 (Translated columns are gap-prefix positions).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall r \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; 0 < n \Rightarrow \left\{X - \operatorname{sortedColumn}\left(C, r\right) \mid x \in C\right\} = \left\{\operatorname{ofNat}\left(n, \operatorname{positivePrefix}\left(\operatorname{rotateWord}\left(\operatorname{gapWord}\left(C\right), r\right), 0, \operatorname{val}\left(i\right)\right)\right) \mid i \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right)\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.support_from_gaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Translate the chosen root column to zero. Every occupied column is then a prefix sum of the rotated gap word, reduced modulo the circumference.

**Theorem 1.2 (Classify a bounded word above the threshold).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \left(5 \le c \land \left(c \le 8 \land \left(\left(\forall i \in \operatorname{Fin}\left(c\right),\; 1 \le \operatorname{h}\left(i\right) \land \operatorname{h}\left(i\right) \le 7\right) \land \left(14 \le \sum _{i \in \operatorname{Fin}\left(c\right)}\operatorname{h}\left(i\right) \land 4 \cdot c + 6 \le \operatorname{T}\left(h\right)\right)\right)\right)\right) \Rightarrow \left(\exists r \in \operatorname{Fin}\left(c\right),\; \exists e \in \operatorname{List}\left(\mathrm{Nat}\right),\; e \in \mathrm{exceptionalRoots} \land \left(\operatorname{length}\left(e\right) = c \land \left(\forall i \in \operatorname{Fin}\left(c\right),\; \operatorname{val}\left(i\right) < \operatorname{length}\left(e\right) \Rightarrow \operatorname{rotateWord}\left(h, r, i\right) = e[\operatorname{val}\left(i\right)]\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.bounded_gap_exception` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A word of five through eight gaps, each between one and seven, with total at least fourteen and score above the parity threshold rotates to an exceptional root.

**Definition 1.3 (The layer state of one column).**

$$\forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(14\right)\right),\; \forall p \in \operatorname{Fin}\left(14\right),\; \operatorname{layerDigit}\left(X, p\right) = \operatorname{if}\left((\mathrm{false}, p) \in X, \operatorname{if}\left((\mathrm{true}, p) \in X, 2, 0\right), 1\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.layerDigit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

An outer-only column has digit zero, an inner-only column has digit one, and a column with both vertices has digit two. A column without an outer vertex is assigned one, including an empty column.

**Definition 1.4 (The list of layer states).**

$$\forall positions \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(14\right)\right),\; \operatorname{layerDigits}\left(positions, X\right) = \operatorname{ofFn}\left((\lambda j:\operatorname{Fin}\left(\operatorname{length}\left(positions\right)\right), \operatorname{layerDigit}\left(X, \operatorname{ofNat}\left(14, positions[\operatorname{val}\left(j\right)]\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.layerDigits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Read the layer state at every listed support position, interpreting its index modulo fourteen.

**Definition 1.5 (Encode the support labels).**

$$\forall positions \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(14\right)\right),\; \operatorname{layerCode}\left(positions, X\right) = \operatorname{ofDigits}\left(3, \operatorname{layerDigits}\left(positions, X\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.layerCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The list of layer digits is encoded as a natural number in base three, with its first digit least significant.

**Definition 1.6 (The columns in a position list).**

$$\forall positions \in \operatorname{List}\left(\mathrm{Nat}\right),\; \operatorname{supportSet}\left(positions\right) = \left\{\operatorname{ofNat}\left(14, positions[\operatorname{val}\left(j\right)]\right) \mid j \in \operatorname{Fin}\left(\operatorname{length}\left(positions\right)\right)\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.supportSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Take the finite set of listed positions after reduction modulo fourteen.

**Theorem 1.7 (Decoding the layer code recovers the set).**

$$\forall positions \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(14\right)\right),\; \left(\left(\forall j \in \operatorname{Fin}\left(\operatorname{length}\left(positions\right)\right),\; positions[\operatorname{val}\left(j\right)] < 14\right) \land \operatorname{columns}\left(X\right) = \operatorname{supportSet}\left(positions\right)\right) \Rightarrow \operatorname{labelledSupport}\left(positions, \operatorname{layerCode}\left(positions, X\right)\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.labelledSupport_layerCode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Every set whose occupied columns are exactly the listed positions is recovered by its layer code, provided all listed positions are below fourteen. No assumption on the number of selected vertices is needed.

**Theorem 1.8 (The direct scan equals requests plus collisions).**

$$\forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(14\right)\right),\; \operatorname{directScore}\left(X\right) = \operatorname{I}\left(14, X\right) + \operatorname{K}\left(14, X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.directScore_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The direct source and destination counts agree with the semantic occupied-request and empty-collision counts.

**Theorem 1.9 (Sizes and reflections of the support lists).**

$$\left(\forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; p \in [\mathrm{positions6}, \mathrm{positions7a}, \mathrm{positions7b}, \mathrm{positions8}] \Rightarrow \left(\left(\forall j \in \operatorname{Fin}\left(\operatorname{length}\left(p\right)\right),\; p[\operatorname{val}\left(j\right)] < 14\right) \land \operatorname{card}\left(\operatorname{supportSet}\left(p\right)\right) = \operatorname{length}\left(p\right)\right)\right) \land \left(\left\{3 - i \mid i \in \operatorname{supportSet}\left(\mathrm{positions7r}\right)\right\} = \operatorname{supportSet}\left(\mathrm{positions7a}\right) \land \left\{3 - i \mid i \in \operatorname{supportSet}\left(\mathrm{positions8r}\right)\right\} = \operatorname{supportSet}\left(\mathrm{positions8}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.canonical_support_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The four canonical lists have distinct positions below fourteen. Reflection i to three minus i in Fin 14 sends positions7r to positions7a and positions8r to positions8.

**Theorem 1.10 (Every exceptional support has circumference fourteen).**

$$\forall n \in \mathrm{Nat},\; \forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall r \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; \forall e \in \operatorname{List}\left(\mathrm{Nat}\right),\; \left(0 < n \land \left(e \in \mathrm{exceptionalRoots} \land \left(\operatorname{length}\left(e\right) = \operatorname{card}\left(C\right) \land \left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(C\right)\right),\; \operatorname{val}\left(i\right) < \operatorname{length}\left(e\right) \Rightarrow \operatorname{rotateWord}\left(\operatorname{gapWord}\left(C\right), r, i\right) = e[\operatorname{val}\left(i\right)]\right)\right)\right)\right) \Rightarrow n = 14$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.exceptionalRoot_circumference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

An exceptional root matching a rotated support word has total equal to the circumference, so that circumference is fourteen.

**Definition 1.11 (Positions determined by gap prefixes).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; 0 < c \Rightarrow \operatorname{wordSupport}\left(h\right) = \left\{\operatorname{ofNat}\left(14, \operatorname{positivePrefix}\left(h, 0, \operatorname{val}\left(i\right)\right)\right) \mid i \in \operatorname{Fin}\left(c\right)\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.wordSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The word support consists of the prefix positions starting at zero, reduced modulo fourteen.

**Theorem 1.12 (The six possible exceptional supports).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall e \in \operatorname{List}\left(\mathrm{Nat}\right),\; \left(0 < c \land \left(e \in \mathrm{exceptionalRoots} \land \left(\operatorname{length}\left(e\right) = c \land \left(\forall i \in \operatorname{Fin}\left(c\right),\; \operatorname{val}\left(i\right) < \operatorname{length}\left(e\right) \Rightarrow \operatorname{h}\left(i\right) = e[\operatorname{val}\left(i\right)]\right)\right)\right)\right) \Rightarrow \left(\exists p \in \operatorname{List}\left(\mathrm{Nat}\right),\; p \in [\mathrm{positions6}, \mathrm{positions7r}, \mathrm{positions7a}, \mathrm{positions7b}, \mathrm{positions8r}, \mathrm{positions8}] \land \operatorname{wordSupport}\left(h\right) = \operatorname{supportSet}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.exceptionalRoot_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A word agreeing with one of the six exceptional roots yields one of the six displayed support lists, including the two reflected variants.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.bounded_gap_exception`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.canonical_support_facts`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.directScore_eq`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.exceptionalRoot_circumference`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.exceptionalRoot_support`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.labelledSupport_layerCode`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.layerCode`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.layerDigit`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.layerDigits`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.supportSet`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.support_from_gaps`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.wordSupport`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData56A](ZeroForcingThreeGapData56A.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData56B](ZeroForcingThreeGapData56B.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7A](ZeroForcingThreeGapData7A.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData7B](ZeroForcingThreeGapData7B.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8A](ZeroForcingThreeGapData8A.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8B](ZeroForcingThreeGapData8B.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapData8C](ZeroForcingThreeGapData8C.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact](ZeroForcingThreeGapExact.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong](ZeroForcingThreeGapLong.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests](ZeroForcingThreeRequests.md)
