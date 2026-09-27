# Sound Bounds for the Mask Recurrence

## Abstract

Every bounded completion inherits the slot-price bound and the classification of accepted large-score leaves.

**Theorem 1.1 (A dual price bounds every completion).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall price \in \mathrm{Nat},\; \left(0 < c \land \left(\left(\forall j \in \operatorname{Fin}\left(c\right),\; \operatorname{val}\left(j\right) < \operatorname{length}\left(p\right) \Rightarrow \operatorname{h}\left(j\right) = p[\operatorname{val}\left(j\right)]\right) \land \left(\forall j \in \operatorname{Fin}\left(c\right),\; 1 \le \operatorname{h}\left(j\right) \land \operatorname{h}\left(j\right) \le m\right)\right)\right) \Rightarrow \operatorname{T}\left(h\right) \le \operatorname{priceBound}\left(\operatorname{maskSlots}\left(c, m, p\right), price\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge.T_le_maskPrice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

For a positive-length word extending the prescribed prefix, with every gap between one and m, every natural dual price bounds T by priceBound of the computed slot list.

**Theorem 1.2 (Accepted large-score completions are exceptional).**

$$\forall c \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall p \in \operatorname{List}\left(\mathrm{Nat}\right),\; \forall h \in \operatorname{Fin}\left(c\right) \to \mathrm{Nat},\; \forall fuel \in \mathrm{Nat},\; \left(0 < c \land \left(\operatorname{length}\left(p\right) + fuel = c \land \left(\left(\forall j \in \operatorname{Fin}\left(c\right),\; \operatorname{val}\left(j\right) < \operatorname{length}\left(p\right) \Rightarrow \operatorname{h}\left(j\right) = p[\operatorname{val}\left(j\right)]\right) \land \left(\left(\forall j \in \operatorname{Fin}\left(c\right),\; 1 \le \operatorname{h}\left(j\right) \land \operatorname{h}\left(j\right) \le m\right) \land \left(\operatorname{maskCheck}\left(c, fuel, m, p\right) = \mathrm{true} \land \left(14 \le \sum _{j \in \operatorname{Fin}\left(c\right)}\operatorname{h}\left(j\right) \land 4 \cdot c + 6 \le \operatorname{T}\left(h\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists e \in \operatorname{List}\left(\mathrm{Nat}\right),\; e \in \mathrm{exceptionalRoots} \land \left(\operatorname{length}\left(e\right) = c \land \left(\forall j \in \operatorname{Fin}\left(c\right),\; \operatorname{val}\left(j\right) < \operatorname{length}\left(e\right) \Rightarrow \operatorname{h}\left(j\right) = e[\operatorname{val}\left(j\right)]\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge.maskCheck_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnav Krishnan (2026). *A correction to the Zero Forcing Number of the Generalized Petersen Graphs P(n,3)*. DOI: [10.48550/arXiv.2607.19412](https://doi.org/10.48550/arXiv.2607.19412). URL: <https://arxiv.org/abs/2607.19412v1>.

*Commentary.*

An accepted completion with total at least fourteen and score at least four times c plus six is exactly one of the exceptional rooted words. Induction on the remaining prefix length carries the pointwise completion through the recurrence.

## References

- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge.T_le_maskPrice`
- Truth anchor: `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapMaskBridge.maskCheck_sound`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapCompute](ZeroForcingThreeGapCompute.md)
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests](ZeroForcingThreeRequests.md)
