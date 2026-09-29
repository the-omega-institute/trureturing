# Every Ten-Vertex Set Has Boundary at Least Eight

## Abstract

Bounded gaps, the fourteen-column long-gap case, and deletion through an empty buffer give a uniform isoperimetric bound.

**Theorem 1.1 (The boundary bound for bounded support gaps).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \left(14 \le n \land \left(\operatorname{card}\left(X\right) = 10 \land \left(5 \le \operatorname{card}\left(\operatorname{columns}\left(X\right)\right) \land \left(\operatorname{card}\left(\operatorname{columns}\left(X\right)\right) \le 8 \land \left(\forall i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{columns}\left(X\right)\right)\right),\; \operatorname{gapWord}\left(\operatorname{columns}\left(X\right), i\right) \le 7\right)\right)\right)\right)\right) \Rightarrow 8 \le \operatorname{card}\left(\operatorname{externalBoundary}\left(n, X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary.bounded_gap_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For a ten-vertex set with five through eight occupied columns and gaps at most seven, the score bound and the exact exceptional-support intervals give external boundary at least eight.

**Theorem 1.2 (Remove one column inside an empty buffer).**

$$\forall m \in \mathrm{Nat},\; \forall t \in \operatorname{Fin}\left(m + 1\right),\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(m + 1\right)\right),\; \left(14 \le m \land \left(\forall v \in \mathrm{Bool}\times \operatorname{Fin}\left(m + 1\right),\; \forall k \in \mathrm{Nat},\; \left(v \in X \land k \le 3\right) \Rightarrow \left(\operatorname{snd}\left(v\right) \ne t + \operatorname{ofNat}\left(m + 1, k\right) \land \operatorname{snd}\left(v\right) \ne t - \operatorname{ofNat}\left(m + 1, k\right)\right)\right)\right) \Rightarrow \left(\exists Y \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(m\right)\right),\; \operatorname{card}\left(Y\right) = \operatorname{card}\left(X\right) \land \left(\operatorname{card}\left(\operatorname{externalBoundary}\left(m, Y\right)\right) = \operatorname{card}\left(\operatorname{externalBoundary}\left(m + 1, X\right)\right) \land \left(\left\{(\operatorname{fst}\left(v\right), \operatorname{succAbove}\left(t, \operatorname{snd}\left(v\right)\right)) \mid v \in Y\right\} = X \land \left(\left\{(\operatorname{fst}\left(v\right), \operatorname{succAbove}\left(t, \operatorname{snd}\left(v\right)\right)) \mid v \in \operatorname{externalBoundary}\left(m, Y\right)\right\} = \operatorname{externalBoundary}\left(m + 1, X\right) \land \left\{\operatorname{succAbove}\left(t, i\right) \mid i \in \operatorname{columns}\left(Y\right)\right\} = \operatorname{columns}\left(X\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary.buffered_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

If no selected column lies within three cyclic steps of t, deletion of t preserves the selected-set cardinality and external-boundary cardinality. The map sending each column through succAbove t recovers the entire selected set, its external boundary, and its occupied columns.

**Theorem 1.3 (The uniform ten-vertex boundary inequality).**

$$\forall n \in \mathrm{Nat},\; \forall X \in \operatorname{Finset}\left(\mathrm{Bool}\times \operatorname{Fin}\left(n\right)\right),\; \left(14 \le n \land \operatorname{card}\left(X\right) = 10\right) \Rightarrow 8 \le \operatorname{card}\left(\operatorname{externalBoundary}\left(n, X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary.p3_ten_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Every ten-vertex set in P(n,3), for n at least fourteen, has at least eight external neighbors. Occupied spoke mates handle at least nine columns; bounded gaps, the fourteen-column long-gap bound, and strong induction using buffered deletion handle the remaining supports.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary.bounded_gap_boundary`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary.buffered_deletion`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeTenBoundary.p3_ten_boundary`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary](ZeroForcingThreeBoundary.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover6G0](ZeroForcingThreeGapCover6G0.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7AG0](ZeroForcingThreeGapCover7AG0.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7AG1](ZeroForcingThreeGapCover7AG1.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7AG2](ZeroForcingThreeGapCover7AG2.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7BG0](ZeroForcingThreeGapCover7BG0.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7BG1](ZeroForcingThreeGapCover7BG1.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover7BG2](ZeroForcingThreeGapCover7BG2.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G0](ZeroForcingThreeGapCover8G0.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G1](ZeroForcingThreeGapCover8G1.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G2](ZeroForcingThreeGapCover8G2.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G3](ZeroForcingThreeGapCover8G3.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G4](ZeroForcingThreeGapCover8G4.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G5](ZeroForcingThreeGapCover8G5.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCover8G6](ZeroForcingThreeGapCover8G6.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong](ZeroForcingThreeGapLong.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport](ZeroForcingThreeGapRootSupport.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests](ZeroForcingThreeRequests.md)
