# Projection Probability Flow

## Abstract

Finite-dimensional Hamiltonian evolution differentiates projection probabilities by the commutator trace and conserves them for commuting projections.

**Theorem 1.1 (Projection probabilities follow the commutator trace).**

$$\begin{gathered}\forall n, H, P, \rho,\\{}\operatorname{Finite}\left(n\right), H, P \in M_{n}(\mathbb{C}), \operatorname{DensityState}\left(\rho, n\right), \operatorname{Hermitian}\left(H\right), \operatorname{StarProjection}\left(P\right),\\{}U_{t} = \operatorname{exp}(- i t H), \rho_{t} = U_{t} \rho U_{t}^*, p_{P}(t) = \Re \operatorname{Tr}(\rho_{t}P) \in \mathbb{R},\\{}(\forall t \in \mathbb{R}, \operatorname{ofReal}\left(p_{P}(t)\right) = \operatorname{Tr}(\rho_{t}P)) \land\\{}(\forall t \in \mathbb{R}, \frac{d}{dt} p_{P}(t) = \Re i \operatorname{Tr}(\rho_{t}[H,P])) \land\\{}(\forall t \in \mathbb{R}, \operatorname{ofReal}\left(\Re i \operatorname{Tr}(\rho_{t}[H,P])\right) = i \operatorname{Tr}(\rho_{t}[H,P])) \land\\{}([H,P] = 0 \Rightarrow \forall t \in \mathbb{R}, p_{P}(t) = p_{P}(0)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.projection_probability_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a positive trace-one state on a finite complex matrix algebra, let H be Hermitian, and let P be a star projection. The propagator is the matrix exponential of -i t H, the evolved state is U_t rho U_t^*, and p_P is the real Born probability.

The first displayed conjunct identifies the complex cast of that real probability with the source Born trace. The next two conjuncts give its real derivative and certify that the complex commutator-trace flow is real, so the derivative equals the source formula exactly.

The final conjunct is independent of the derivative clauses: if the Hamiltonian and projection commute, the probability is constant for every real time.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.projection_probability_flow`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
