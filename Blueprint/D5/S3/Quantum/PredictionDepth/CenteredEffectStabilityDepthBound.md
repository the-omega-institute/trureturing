# Finite Stability Depth of the Centered-Effect Tower

## Abstract

A finite centered-effect tower reaches its terminal predictive space within its dimension gap.

**Theorem 1.1 (The first stable depth is bounded by visible dimension growth).**

$$\begin{gathered}\forall d, r: \operatorname{Nat}, d \geq 1,\\{}H: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianTraceZero}(d), \operatorname{HermitianTraceZero}(d)), E: \operatorname{Fin}(r+1) \to\operatorname{HermitianTraceZero}(d),\\{}\operatorname{stabilityDepth}(H, E) \leq \operatorname{finrank}(\mathbb{R}, \operatorname{predictiveSpace}(H, E)) - \operatorname{finrank}(\mathbb{R}, \operatorname{towerSpace}(H, E, 0)) \land\\{}\operatorname{finrank}(\mathbb{R}, \operatorname{predictiveSpace}(H, E)) - \operatorname{finrank}(\mathbb{R}, \operatorname{towerSpace}(H, E, 0)) \leq d^{2} - 1 - \operatorname{finrank}(\mathbb{R}, \operatorname{towerSpace}(H, E, 0)) \land\\{}\operatorname{predictiveSpace}(H, E) = \operatorname{iSupTowerSpace}(H, E) \land\\{}\operatorname{iSupTowerSpace}(H, E) = \operatorname{towerSpace}(H, E, \operatorname{stabilityDepth}(H, E)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/CenteredEffectStabilityDepthBound.centered_effect_stability_depth_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the imported real HermitianTraceZero(d) space. The finite stage towerSpace(H,E,m) is generated recursively from the centered effects, while predictiveSpace(H,E) is the real span of all finite Heisenberg iterates.

The public stabilityDepth(H,E) is the infimum of the natural indices m for which towerSpace(H,E,m) equals towerSpace(H,E,m+1). Finite dimension makes this test nonempty, and one-step stability is permanent by the imported tower theorem.

Every strict stage inclusion raises real finrank by at least one. Thus the least stable index is at most the terminal finrank gain. The exact trace-zero Hermitian dimension d squared minus one gives the second bound on the same source carrier.

The final two displayed clauses identify predictiveSpace(H,E) first with the supremum of all finite tower stages and then identify that supremum with the stage at stabilityDepth(H,E). Repository and pinned-library searches found no theorem packaging these four clauses; the proof applies the existing carrier, tower, predictive space, finrank, and natural-infimum declarations directly.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/CenteredEffectStabilityDepthBound.centered_effect_stability_depth_bound`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Fibers/MinimalPredictiveSummary](../Fibers/MinimalPredictiveSummary.md)
