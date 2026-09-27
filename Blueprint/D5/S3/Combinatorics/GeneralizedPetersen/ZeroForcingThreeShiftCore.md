# Columns and Cyclic Neighbor Shifts

## Abstract

Column support and the two layer-dependent shifts organize requests from selected vertices.

**Definition 1.1 (Occupied columns).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \operatorname{columns}\left(X\right) = \left\{\operatorname{snd}\left(v\right) \mid v \in X\right\}$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.columns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Project the selected vertices onto their column indices.

**Definition 1.2 (Both vertices of every occupied column).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \operatorname{occupiedVertices}\left(X\right) = \mathrm{Bool}\times \operatorname{columns}\left(X\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.occupiedVertices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For each occupied column, include both its outer and inner vertex.

**Definition 1.3 (Forward layer neighbor).**

$$\forall n \in \mathrm{Nat},\; \forall v \in \mathrm{Bool}\times \operatorname{Fin}\left(n\right),\; 0 < n \Rightarrow \operatorname{positiveShift}\left(n, v\right) = (\operatorname{fst}\left(v\right), \operatorname{snd}\left(v\right) + \operatorname{ofNat}\left(n, \operatorname{if}\left(\operatorname{fst}\left(v\right) = \mathrm{true}, 3, 1\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.positiveShift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The equivalence adds one in the outer layer and three in the inner layer, with arithmetic modulo n.

**Definition 1.4 (Backward layer neighbor).**

$$\forall n \in \mathrm{Nat},\; \forall v \in \mathrm{Bool}\times \operatorname{Fin}\left(n\right),\; 0 < n \Rightarrow \operatorname{negativeShift}\left(n, v\right) = (\operatorname{fst}\left(v\right), \operatorname{snd}\left(v\right) - \operatorname{ofNat}\left(n, \operatorname{if}\left(\operatorname{fst}\left(v\right) = \mathrm{true}, 3, 1\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.negativeShift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The inverse of positiveShift subtracts the corresponding layer step modulo n.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.columns`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.negativeShift`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.occupiedVertices`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore.positiveShift`
