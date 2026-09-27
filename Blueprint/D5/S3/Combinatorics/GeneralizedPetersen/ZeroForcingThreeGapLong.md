# Fourteen-Column Words with a Long Gap

## Abstract

Rotating a long gap to the root reduces its score bound to positive compositions of fourteen.

**Definition 1.1 (Cyclic rotation of a gap word).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall r \in \operatorname{Fin}\left(c\right),\; \forall i \in \operatorname{Fin}\left(c\right),\; \operatorname{rotateWord}\left(h, r, i\right) = \operatorname{h}\left(r + i\right)$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.rotateWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

The rotated word starts at r and retains the cyclic order of the gaps.

**Definition 1.2 (Rotation as an index equivalence).**

$$\forall c \in \mathrm{Nat},\; \forall r \in \operatorname{Fin}\left(c\right),\; \forall i \in \operatorname{Fin}\left(c\right),\; 0 < c \Rightarrow \operatorname{rotation}\left(r, i\right) = r + i$$

*Formalization.* `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.rotation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

Cyclic addition by r is an equivalence of Fin c; its inverse subtracts r.

**Theorem 1.3 (A long gap bounds the ten-slot score).**

$$\forall c \in \mathrm{Nat},\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall r \in \operatorname{Fin}\left(c\right),\; \left(5 \le c \land \left(c \le 8 \land \left(\left(\forall i \in \operatorname{Fin}\left(c\right),\; 1 \le \operatorname{h}\left(i\right)\right) \land \left(\sum _{i \in \operatorname{Fin}\left(c\right)}\operatorname{h}\left(i\right) = 14 \land 8 \le \operatorname{h}\left(r\right)\right)\right)\right)\right) \Rightarrow \operatorname{T}\left(h\right) \le 4 \cdot c + 5$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.long_gap_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

A positive cyclic word with five through eight entries, total fourteen, and an entry at least eight has T at most four times its length plus five. The rooted positive-composition family contains twenty-two words.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.long_gap_score`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.rotateWord`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapLong.rotation`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge](ZeroForcingThreeGapMaskBridge.md)
