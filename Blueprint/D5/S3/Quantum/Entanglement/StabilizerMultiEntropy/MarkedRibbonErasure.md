# Recorded deletion and recordless erasure on a fixed ribbon phase graph

## Abstract

Recorded deletion and recordless erasure on a fixed phase graph for a literal marked ribbon.

**Theorem 1.1 (One fixed chart controls recorded deletion and recordless erasure).**

$$\forall R \in \operatorname{FiniteLiteralMarkedSignedRibbons}\left(\right),\; \exists C \in \operatorname{ExtractedSignedCharts}\left(R\right),\; \forall s \in \operatorname{ChartStateMasks}\left(C\right),\; \operatorname{ObservedRecordedPurityAndRecordlessEntries}\left(C, s\right) = \operatorname{LiteralBoundaryPowerAndSyndromePhaseEntries}\left(R, C, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure.actual_ribbon_two_deletions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a signed spanning-forest chart for each physical flag component once. Its binary pairing is the adjacency between two distinct banks; diagonal twist entries are ordinary cross-bank edges. The selected mask only chooses which coordinates of the prebuilt phase graph are retained. Pauli Z feed-forward cancels the two mixed phases for every available computational-basis deletion outcome.

The theorem combines the exact recordless coordinate entry with the purity of the outcome-conditioned left marginal. The trace of the square of that marginal is the relative size of the kernel of the restricted pairing. The binary Cohn–Lempel identity and literal state switch turn the product of these purities, multiplied by the two-power of the component and selected-band count, into the exact two-power of the original boundary-circle count. The phase graph is block diagonal across disconnected components. This is not an operational sample-complexity or Jones-normalization claim.

**Theorem 1.2 (Exact retained phase state within each recordless erasure coset).**

$$\forall G \in \operatorname{FourBinaryPhaseBlocks}\left(\right),\; \forall v \in \operatorname{TranslatedSyndromeKernelCoordinates}\left(G\right),\; \operatorname{LocallyCorrectedErasedEntry}\left(G, v\right) = \operatorname{PurePhaseEntryWeightedBySyndrome}\left(G, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure.erased_coset_corrected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed graph-state partial trace cancels all entries with distinct cross-phase syndromes by binary character orthogonality. Each surviving syndrome block is a subnormalized pure graph-phase block on the two kernels; explicit local signs remove the coset representatives. The proof operates on the normalized rank-one computational-basis projector before erasure, not on an assumed rank oracle.

If the two cross-couplings are injective, the retained density is completely diagonal regardless of the retained pairing. Thus this zero-record operation has genuinely different information content from recorded deletion. Standard pure graph-state cut rank and Pauli deletion are due to Hein, Eisert and Briegel, Phys. Rev. A 69, 062311 (2004); the bridge here accounts for the signed literal ribbon and exact mixed erasure blocks.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure.actual_ribbon_two_deletions`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonErasure.erased_coset_corrected`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments](DiagonalLinearCodeMoments.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonJointMoments](MarkedRibbonJointMoments.md)
