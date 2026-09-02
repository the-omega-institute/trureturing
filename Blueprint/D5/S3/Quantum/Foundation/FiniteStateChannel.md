# Finite Density States and Quantum Channels

## Abstract

Canonical finite density states and completely positive trace-preserving channels.

**Theorem 1.1 (Channel composition agrees with sequential state evolution).**

$$\operatorname{mapState}(\phi_{2} \circ \phi_{1}, \rho) = \operatorname{mapState}(\phi_{2}, \operatorname{mapState}(\phi_{1}, \rho))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteStateChannel.channel_comp_mapState` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A density state is a positive semidefinite CStarMatrix of trace one. A channel is a Mathlib completely positive map equipped with trace preservation.

Complete positivity sends density matrices to positive matrices and trace preservation retains normalization, giving a canonical state action.

Composition uses Mathlib's amplified positivity interface. Applying the composed channel to a density state equals applying the two channels sequentially.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteStateChannel.channel_comp_mapState`
