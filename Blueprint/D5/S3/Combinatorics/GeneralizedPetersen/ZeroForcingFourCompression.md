# Radius-Four Column Compression

## Abstract

Deleting the middle of nine empty cyclic columns preserves selected neighborhoods and the external boundary in P(n,4). The symbolic compression argument follows Wenlin Zhang and Haobo Ma.

**Definition 1.1 (Insert a missing column).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \operatorname{Fin}\left(m + 1\right),\; \forall v \in \mathrm{Bool}\times \operatorname{Fin}\left(m\right),\; \operatorname{insertVertex}\left(t, v\right) = (\operatorname{fst}\left(v\right), \operatorname{succAbove}\left(t, \operatorname{snd}\left(v\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.insertVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The order-preserving insertion acts on the column index and preserves the layer.

**Definition 1.2 (A nine-column empty buffer).**

$$\forall n \in \mathrm{Nat},\; [\operatorname{NeZero}\left(n\right)] \forall t \in \operatorname{Fin}\left(n\right),\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \operatorname{EmptyBuffer}\left(t, X\right) \Leftrightarrow \left(\forall v \in \mathrm{Bool}\times \operatorname{Fin}\left(n\right),\; \forall d \in \mathrm{Nat},\; \left(v \in X \land d \le 4\right) \Rightarrow \left(\operatorname{snd}\left(v\right) \ne t + \operatorname{ofNat}\left(n, d\right) \land \operatorname{snd}\left(v\right) \ne t - \operatorname{ofNat}\left(n, d\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.EmptyBuffer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The center and the four columns on either cyclic side contain no selected vertex. The condition applies at every cyclic position, including either end of the chosen numbering.

**Theorem 1.3 (Exact neighborhood and boundary transport).**

$$\forall m \in \mathrm{Nat},\; [\operatorname{NeZero}\left(m\right)] \forall t \in \operatorname{Fin}\left(m + 1\right),\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(m + 1\right)\right),\; \left(108 \le m \land \operatorname{EmptyBuffer}\left(t, X\right)\right) \Rightarrow \left(\exists Y \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(m\right)\right),\; \operatorname{card}\left(Y\right) = \operatorname{card}\left(X\right) \land \left(\operatorname{card}\left(\operatorname{externalBoundary}\left(\operatorname{gp}\left(m, 4\right), Y\right)\right) = \operatorname{card}\left(\operatorname{externalBoundary}\left(\operatorname{gp}\left(m + 1, 4\right), X\right)\right) \land \left(\left\{\operatorname{insertVertex}\left(t, v\right) \mid v \in Y\right\} = X \land \left(\left\{\operatorname{insertVertex}\left(t, v\right) \mid v \in \operatorname{externalBoundary}\left(\operatorname{gp}\left(m, 4\right), Y\right)\right\} = \operatorname{externalBoundary}\left(\operatorname{gp}\left(m + 1, 4\right), X\right) \land \left(\left\{\operatorname{succAbove}\left(t, i\right) \mid i \in \operatorname{columns}\left(Y\right)\right\} = \operatorname{columns}\left(X\right) \land \left(\forall u \in \mathrm{Bool}\times \operatorname{Fin}\left(m\right),\; \forall v \in \mathrm{Bool}\times \operatorname{Fin}\left(m\right),\; u \in Y \Rightarrow \left(\operatorname{Adj}\left(\operatorname{gp}\left(m, 4\right), u, v\right) \Leftrightarrow \operatorname{Adj}\left(\operatorname{gp}\left(m + 1, 4\right), \operatorname{insertVertex}\left(t, u\right), \operatorname{insertVertex}\left(t, v\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.buffered_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Every selected incident edge is preserved in both directions: outer steps of one, inner steps of four, and spokes. Every old neighbor survives, and each new neighbor has a unique old lift. Insertion recovers the entire selected set, external boundary, and column support, so both cardinalities are equal.

**Theorem 1.4 (Compress a hypothetical small-boundary set to 108 columns).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \left(109 \le n \land \left(\operatorname{card}\left(X\right) = 16 \land \operatorname{card}\left(\operatorname{externalBoundary}\left(\operatorname{gp}\left(n, 4\right), X\right)\right) \le 9\right)\right) \Rightarrow \left(\exists Y \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(108\right)\right),\; \operatorname{card}\left(Y\right) = 16 \land \operatorname{card}\left(\operatorname{externalBoundary}\left(\operatorname{gp}\left(108, 4\right), Y\right)\right) = \operatorname{card}\left(\operatorname{externalBoundary}\left(\operatorname{gp}\left(n, 4\right), X\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.compression_to_108` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Spokes place every unselected vertex of an occupied column in the boundary, giving at most twelve occupied columns. Their nine cyclic translates cover at most 108 possible buffer centers. Above 108 columns a center remains outside that cover. Exact buffered deletion and strong induction reduce to 108, preserving the selected and boundary cardinalities. This implication makes no assumption about finite certificates and proves no finite boundary exclusion or zero forcing number.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.EmptyBuffer`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.buffered_deletion`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.compression_to_108`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingFourCompression.insertVertex`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree](ZeroForcingThree.md)
