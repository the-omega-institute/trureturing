# Computational-Basis Kernel Preservation

## Abstract

Basis fiber projectors preserve the deterministic readout kernel.

**Theorem 1.1 (Fiber projectors retain exactly the deterministic kernel).**

$$\begin{gathered}\forall X: \operatorname{Type}, O: \operatorname{Type},\\{}[\operatorname{Fintype}(X)], [\operatorname{DecidableEq}(X)], [\operatorname{DecidableEq}(O)],\\{}q: X \to O, x: X, y: X,\\{}\operatorname{let}(\rho: X \to \operatorname{Matrix}(X, X, \mathbb{C}), \forall z: X, \rho(z) = \operatorname{basisProjector}(z),\\{}P: O \to \operatorname{Matrix}(X, X, \mathbb{C}), \forall o: O, P(o) = \sum_{z \in X, q(z) = o} \operatorname{basisProjector}(z))\;[\forall o: O, \operatorname{Tr}(\operatorname{mul}(\rho(x), P(o))) = \operatorname{indicator}(q(x) = o)] \land\\{}[q(x) = q(y) \iff \forall o: O, \operatorname{Tr}(\operatorname{mul}(\rho(x), P(o))) = \operatorname{Tr}(\operatorname{mul}(\rho(y), P(o)))].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ComputationalBasisKernelPreservation.computational_basis_kernel_preservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite state type and O an outcome type with decidable equality. The density matrix rho of a state is the canonical coordinate rank-one projector.

For each outcome, its projector is constructed as the finite sum of coordinate projectors over the corresponding q-fiber. The trace pairing with rho is therefore the fiber indicator.

Equality of every outcome probability follows from equal q-values. Conversely, evaluating the common signature at q(x) forces the two q-values to agree.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ComputationalBasisKernelPreservation.computational_basis_kernel_preservation`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
