# Invariant States of Finite-Dimensional Channels

## Abstract

Positive trace-preserving finite-dimensional matrix maps admit invariant states.

**Theorem 1.1 (Positive trace-preserving matrix maps admit invariant states).**

$$\forall n\ [\operatorname{Fintype}(n)] [\operatorname{Nonempty}(n)],\ \forall \phi: \operatorname{LinearMap}_{\mathbb{C}}(M_{n}(\mathbb{C}), M_{n}(\mathbb{C})),\ (\forall \rho,\ \operatorname{PosSemidef}(\rho) \Rightarrow \operatorname{PosSemidef}(\phi(\rho))) \land (\forall \rho,\ \operatorname{tr}(\phi(\rho))=\operatorname{tr}(\rho)) \Rightarrow \exists \rho,\ \operatorname{PosSemidef}(\rho) \land \operatorname{tr}(\rho)=1 \land \phi(\rho)=\rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ChannelFixedState.channel_fixed_state_exists` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information*. DOI: [10.1017/9781316848142](https://doi.org/10.1017/9781316848142).

*Commentary.*

Let n be a nonempty finite index type. Every complex-linear endomorphism of the n-by-n complex matrices that preserves positive semidefiniteness and trace has a positive semidefinite trace-one fixed point. Complete positivity is not assumed. The proof starts from the normalized identity and forms the Cesaro averages of its forward orbit. Positivity and trace preservation keep every average in the state space; nonnegative eigenvalues summing to one bound the operator norm, so finite-dimensional compactness supplies a convergent subsequence. The difference between an average and its image is a telescoping endpoint term divided by the averaging length and therefore tends to zero, forcing the subsequential limit to be fixed. This is a linear-algebraic compactness proof and does not invoke Brouwer's fixed-point theorem. Watrous, The Theory of Quantum Information (2018), Section 4.4, supplies the literature anchor for the standard finite-dimensional channel fixed-point setting. This theorem is only the invariant-state existence base: the pure-fixed-point premise of Theorem 4.5, complete positivity, the tangent factor, and equivalence with an interior faithful invariant state remain separate open obligations.

## References

- Truth anchor: `D5/S3/Quantum/ChannelFixedState.channel_fixed_state_exists`
