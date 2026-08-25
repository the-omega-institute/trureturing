# Conservation And Autonomy Are Distinct

## Abstract

Conservation of one observable is distinct from autonomy of an observable space.

**Theorem 1.1 (An autonomous observable space need not be stationary).**

$$\forall n, \operatorname{finite}\left(n\right), H, A \in \operatorname{Mat}\left(n, C\right), \operatorname{star}\left(H\right) = H, \operatorname{star}\left(A\right) = A,\\{}([H, A] = 0 \Rightarrow \forall t\in R, \operatorname{U}\left(H, -t\right) A \operatorname{U}\left(H, t\right) = A) \land (\operatorname{star}\left(Z\right) = Z \land \operatorname{star}\left(X\right) = X \land X \in \operatorname{ker}\left(tr\right) \land\\{}(\forall B \in \operatorname{ker}\left(tr\right), [Z, B] \in \operatorname{ker}\left(tr\right)) \land [Z, X] \neq 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ConservationAutonomySeparation.conservation_and_autonomy_are_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite complex matrices, a zero Hamiltonian commutator makes the Heisenberg conjugation of the observable constant at every real time.

The explicit contrast uses the self-adjoint qubit Z and X matrices. The trace-zero observable space contains X and is preserved by commutation with Z, while the commutator of Z and X is nonzero.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ConservationAutonomySeparation.conservation_and_autonomy_are_distinct`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
