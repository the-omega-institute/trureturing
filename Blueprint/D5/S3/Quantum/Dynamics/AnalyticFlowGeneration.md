# Analytic Flow Generation

## Abstract

Finite-dimensional Hamiltonian flow spans its nested commutator closure.

**Theorem 1.1 (Hamiltonian flow generates the commutator closure).**

$$\begin{gathered}\forall n: \operatorname{Type}, \operatorname{Fintype}(n), \operatorname{DecidableEq}(n),\\{}H: \operatorname{Matrix}(n, n, \mathbb{C}), initial: \operatorname{Submodule}(\mathbb{C}, \operatorname{Matrix}(n, n, \mathbb{C})),\\{}\operatorname{span}(\mathbb{C}, \{A | (\exists t\in \mathbb{R}, E\in initial, A = \operatorname{hamiltonianPropagator}(H, -t) E \operatorname{hamiltonianPropagator}(H, t))\}) = \operatorname{iSup}(k \in \mathbb{N}, \operatorname{map}(initial, (\operatorname{mulLeft}(\mathbb{C}, H) - \operatorname{mulRight}(\mathbb{C}, H))^k)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AnalyticFlowGeneration.analytic_flow_generates_commutator_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a finite complex matrix and let initial be a complex subspace of observables. The orbit is constructed from the canonical Hamiltonian propagator, with no chosen basis or auxiliary closure object.

The complex span of all real-time conjugates of initial equals the supremum of its images under every power of the canonical left-minus-right multiplication endomorphism.

Finite dimensionality makes the generated subspaces closed. Difference quotients recover the commutator generator from the flow, while the exponential series and uniqueness for the linear ordinary differential equation recover every flow point from the power orbit.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/AnalyticFlowGeneration.analytic_flow_generates_commutator_closure`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
