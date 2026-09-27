# Exact Layer Codes on Exceptional Supports

## Abstract

Base-three labels select the outer, inner, or both vertices at each support column.

**Definition 1.1 (The positions6 support).**

$$\mathrm{positions6} = [0, 6, 8, 9, 11, 12]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions6` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

This ordered list gives the 6 support positions at circumference fourteen.

**Definition 1.2 (The positions7a support).**

$$\mathrm{positions7a} = [0, 3, 6, 8, 9, 11, 12]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions7a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

This ordered list gives the 7 support positions at circumference fourteen.

**Definition 1.3 (The positions7b support).**

$$\mathrm{positions7b} = [0, 6, 8, 9, 10, 11, 12]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions7b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

This ordered list gives the 7 support positions at circumference fourteen.

**Definition 1.4 (The positions8 support).**

$$\mathrm{positions8} = [0, 3, 6, 8, 9, 10, 11, 12]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions8` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

This ordered list gives the 8 support positions at circumference fourteen.

**Definition 1.5 (The positions7r support).**

$$\mathrm{positions7r} = [0, 3, 5, 6, 8, 9, 11]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions7r` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

This ordered list gives the 7 support positions at circumference fourteen.

**Definition 1.6 (The positions8r support).**

$$\mathrm{positions8r} = [0, 3, 5, 6, 7, 8, 9, 11]$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions8r` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

This ordered list gives the 8 support positions at circumference fourteen.

**Definition 1.7 (A base-three digit).**

$$\forall code \in \mathrm{Nat},\; \forall j \in \mathrm{Nat},\; \operatorname{labelDigit}\left(code, j\right) = \operatorname{div}\left(code, 3^{j}\right) \bmod 3$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.labelDigit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The digit at position j is obtained by natural-number division by three to the jth power, followed by reduction modulo three.

**Definition 1.8 (Decode a layer assignment).**

$$\forall positions \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall code \in \mathrm{Nat},\; \operatorname{labelledSupport}\left(positions, code\right) = \{ v \in \mathrm{Bool}\times \operatorname{Fin}\left(14\right)| \exists j \in \mathrm{Nat},\; j < \operatorname{length}\left(positions\right) \land \left(\operatorname{val}\left(\operatorname{snd}\left(v\right)\right) = positions[j] \land \left(\left(\operatorname{fst}\left(v\right) = \mathrm{true} \land \operatorname{labelDigit}\left(code, j\right) \ne 0\right) \lor \left(\operatorname{fst}\left(v\right) = \mathrm{false} \land \operatorname{labelDigit}\left(code, j\right) \ne 1\right)\right)\right)\} $$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.labelledSupport` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Digit zero selects only the outer vertex, digit one only the inner vertex, and digit two both vertices at the corresponding column.

**Definition 1.9 (Count occupied requests and empty collisions).**

$$\forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(14\right)\right),\; \operatorname{directScore}\left(X\right) = \operatorname{card}\left(\{ v \in X| \operatorname{snd}\left(\operatorname{positiveShift}\left(14, v\right)\right) \in \operatorname{columns}\left(X\right)\} \right) + \operatorname{card}\left(\{ v \in X| \operatorname{snd}\left(\operatorname{negativeShift}\left(14, v\right)\right) \in \operatorname{columns}\left(X\right)\} \right) + \operatorname{card}\left(\{ v \in \mathrm{Bool}\times \operatorname{Fin}\left(14\right)| \left(\neg \operatorname{snd}\left(v\right) \in \operatorname{columns}\left(X\right)\right) \land \left(\operatorname{negativeShift}\left(14, v\right) \in X \land \operatorname{positiveShift}\left(14, v\right) \in X\right)\} \right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.directScore` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Count forward requests into occupied columns, backward requests into occupied columns, and vertices in empty columns receiving requests from both directions.

**Definition 1.10 (The exact score test for one label code).**

$$\forall positions \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall code \in \mathrm{Nat},\; \operatorname{exactRow}\left(positions, code\right) = \mathrm{true} \Leftrightarrow \left(\operatorname{card}\left(\operatorname{labelledSupport}\left(positions, code\right)\right) \ne 10 \lor \operatorname{directScore}\left(\operatorname{labelledSupport}\left(positions, code\right)\right) \le 2 \cdot \operatorname{length}\left(positions\right) + 2\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.exactRow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Only decoded sets of size ten require the bound on directScore; all other cardinalities satisfy the test automatically.

**Definition 1.11 (A consecutive interval of label codes).**

$$\forall positions \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall start \in \mathrm{Nat},\; \forall count \in \mathrm{Nat},\; \operatorname{exactChunk}\left(positions, start, count\right) = \mathrm{true} \Leftrightarrow \left(\forall j \in \mathrm{Nat},\; j < count \Rightarrow \operatorname{exactRow}\left(positions, start + j\right) = \mathrm{true}\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.exactChunk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Every code from start through start plus count minus one must satisfy exactRow.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.directScore`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.exactChunk`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.exactRow`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.labelDigit`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.labelledSupport`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions6`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions7a`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions7b`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions7r`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions8`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapExact.positions8r`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore](ZeroForcingThreeShiftCore.md)
