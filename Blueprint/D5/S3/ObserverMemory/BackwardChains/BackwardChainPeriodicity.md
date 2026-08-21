# Backward Chain Periodicity

## Abstract

An infinite compatible backward chain exists exactly at a periodic point.

**Theorem 1.1 (Infinite backward chains are exactly periodic points).**

$$\forall Y, [\operatorname{Finite} Y],\ tau: Y \to Y, y: Y,\ InfiniteBackwardChain(tau, y) \Leftrightarrow y \in \operatorname{periodicPts}(tau).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/BackwardChains/BackwardChainPeriodicity.infinite_backward_chain_iff_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite state carrier and a self-map tau, an infinite backward chain is a natural-number-indexed family whose next state maps to the current state, with coordinate zero equal to the displayed point.

The canonical backward-orbit theorem identifies coordinate-zero values of all such chains with the periodic-point subtype. Applying its coordinate periodicity and surjectivity clauses gives the two directions of the displayed equivalence directly.

Repository search found the exact declaration BackwardOrbitCore.backward_orbit_eval_zero_bijective and applied it; no additional library theorem was needed.

## References

- Truth anchor: `D5/S3/ObserverMemory/BackwardChains/BackwardChainPeriodicity.infinite_backward_chain_iff_periodic`
- Dependency: [D5/S3/ObserverMemory/InverseLimits/BackwardOrbitCore](../InverseLimits/BackwardOrbitCore.md)
