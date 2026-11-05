# Complete native protocols and arbitrary position cuts

## Abstract

Physical Born normalization for the complete original sixteen-bit protocol tree.

**Theorem 1.1 (The complete original tree has unit total mass and every acquired event has its actual cut trace).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Function}\left(\operatorname{Path}\left(T\right), \operatorname{Bool}\left(\right)\right), (\forall I: \operatorname{Finset}\left(\operatorname{Fin}\left(16\right)\right), ((((\sum_{p \in \operatorname{Path}\left(T\right)} \sum_{z \in \operatorname{Basis}\left(\right)} \operatorname{mass}\left(T, p, z\right) = 1) \land ((0 \leq \operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right)) \land (\operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right) \leq 1))) \land \operatorname{PosSemidef}\left(\operatorname{eventCut}\left(T, I, e\right)\right)) \land (\operatorname{trace}\left(\operatorname{eventCut}\left(T, I, e\right)\right) = \operatorname{complex}\left(\operatorname{eventMass}\left(T, \operatorname{historyEvent}\left(e\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_complete_born_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

The objects are the original NativeProtocolGraft.Tree, Basis, omega0, gate, callMatrix, projector, Path and mass. Basis consists of all sixteen-bit words at the shifted original positions. The unique fixed root has ones at positions 0, 4 and 8. The proof uses the full matrices at every address in Fin 14, rather than a two-dimensional model supplied as an additional premise.

On each active center-bit pair the actual gate coefficients are a,b,c from the existing calibration calculation. Their existing squared norms, the golden quadratic identity and the actual phase norm give orthogonal unit rows. The remaining control blocks are zero or identity before the phase gate. Reindexing the full carrier by the center-bit involution proves exact energy conservation. Forward calls use this identity and inverse syntax uses nine iterations of the same actual matrix. The original resource counter still charges nine calls; no semantic equality with a separately defined matrix inverse is asserted.

The sum of all terminal squared amplitudes is conserved for every incoming full-carrier vector. Its proof recurses over the original finite tree. Each gate preserves energy, and each selector projector keeps precisely one outcome for every basis word, so the complete outcome sum preserves energy exactly. Each child can have its own feedback addresses, depth and stopping label. Unused outcomes, zero vectors, refusals, failures and early stops remain in the original Path type and its sum. No total-probability, gate-unitarity or projector-completeness certificate is an input.

Applying that conservation to the original normalized computational root gives unit total Born mass, including every final computational result. An acquired event is a Boolean function of the original prefix path, independent of any future report. Positivity of squared amplitudes and domination by the complete sum give its mass between zero and one. Any declared complete prefix is itself such a Tree; the theorem therefore applies at that same common cut.

For any subset I of the sixteen positions, including the empty and full subsets, splitAt is the pinned equivalence restricting a word to I and its complement. The row and complement bases are Boolean functions on those two actual position subtypes. Their dimensions are two to the cardinality of I and two to the cardinality of its complement. cutReduced is the existing right partial trace of the outer product of the same actual branch vector after this coordinate equivalence. eventCut sums those matrices over exactly the acquired histories. The existing partial-trace positivity and trace theorems supply positive semidefiniteness and equality of its complex trace with the real event mass. This reduction is a mathematical marginal and adds no physical record deletion, new register or coherent sum of distinct histories.

This is a partial consequence of V88 definitions 23.1 and 23.2 and the physical trace premise used in theorem 24.1. It does not prove the actual cut determinant lower bound, either minimum-eigenvalue lower bound, a faithful-cut existence statement, or the five-call reference-history and full-record Petz compiler. The arithmetic lower bound for a positive raw event remains the existing original_event_resource_bounds result. The full source atom remains open and uncovered.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolBornNormalization.original_complete_born_law`
- Dependency: [D5/S3/Quantum/Dynamics/NativeProtocolCalibration](NativeProtocolCalibration.md)
