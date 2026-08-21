# Backward Chain And Layer Periodicity

## Abstract

Infinite backward chains and every predecessor layer characterize periodic points.

**Theorem 1.1 (Backward chains and all predecessor layers are exactly periodic points).**

$$\forall Y, [\operatorname{Finite} Y],\ tau: Y \to Y, y: Y,\ (InfiniteBackwardChain(tau, y) \Leftrightarrow y \in \operatorname{periodicPts}(tau)) \land ((\forall k\in \mathbb{N},\ \operatorname{Nonempty}(PredecessorLayer(tau, y, k))) \Leftrightarrow y \in \operatorname{periodicPts}(tau)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/BackwardChains/BackwardChainLayerPeriodicity.backward_chain_and_layer_iff_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier and a self-map tau, the predecessor layer at depth k is the set of states x satisfying tau iterated k times at x equals y. The public theorem states both the infinite compatible backward-chain equivalence and the arbitrary-depth nonempty-layer equivalence.

The chain equivalence is imported from the canonical backward-chain theorem. For the layer direction, a layer at the carrier cardinality lies in the stabilized iterate range, whose canonical finite-image theorem identifies that range with the periodic-point set. A canonical backward orbit supplies a witness in every layer for the converse.

Repository search found and directly applied the exact declarations BackwardChainPeriodicity.infinite_backward_chain_iff_periodic, BackwardOrbitCore.backward_iterate_apply, and StableImagePeriodicCore.iterate_range_card_antitone_and_stable. Pinned Mathlib search found the applied periodic-point and finite-pigeonhole ingredients; no single library theorem packaged both public equivalences.

## References

- Truth anchor: `D5/S3/ObserverMemory/BackwardChains/BackwardChainLayerPeriodicity.backward_chain_and_layer_iff_periodic`
- Dependency: [D5/S3/ObserverMemory/BackwardChains/BackwardChainPeriodicity](BackwardChainPeriodicity.md)
- Dependency: [D5/S3/ObserverMemory/InverseLimits/StableImagePeriodicCore](../InverseLimits/StableImagePeriodicCore.md)
