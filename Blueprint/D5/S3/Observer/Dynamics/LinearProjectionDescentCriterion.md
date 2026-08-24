# Linear Projection Descent Criterion

## Abstract

Orthogonal-projection descent is exactly vanishing directed flow, and self-adjoint dynamics make it commutation.

**Theorem 1.1 (Projection descent, directed flow, and commutation).**

$$\begin{gathered}\forall n, P, T: \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\\{}(\operatorname{IsIdempotentElem}\left(P\right) \land \operatorname{IsHermitian}\left(P\right)) \Rightarrow (\operatorname{TFAE}\left(\operatorname{EffectiveDescent}\left(\operatorname{toLin}\left(P\right), \operatorname{toLin}\left(T\right)\right), \operatorname{InterfaceCongruence}\left(\operatorname{toLin}\left(P\right), \operatorname{toLin}\left(T\right)\right), \operatorname{NoCarry}\left(\operatorname{toLin}\left(P\right), \operatorname{toLin}\left(T\right)\right), \operatorname{FactorsThrough}\left(\operatorname{compose}\left(\operatorname{toLin}\left(P\right), \operatorname{toLin}\left(T\right)\right), \operatorname{toLin}\left(P\right)\right), \operatorname{PullbackInvariant}\left(\operatorname{toLin}\left(P\right), \operatorname{toLin}\left(T\right)\right), \operatorname{depthZeroKernel}\left(\operatorname{toLin}\left(P\right)\right) = \operatorname{depthOneKernel}\left(\operatorname{toLin}\left(P\right), \operatorname{toLin}\left(T\right)\right), P \cdot T \cdot (1-P) = 0\right) \land\\{}(\operatorname{IsHermitian}\left(T\right) \Rightarrow (P \cdot T \cdot (1-P) = 0 \Leftrightarrow P \cdot T-T \cdot P = 0))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Dynamics/LinearProjectionDescentCriterion.linear_projection_descent_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the finite complex Hilbert space of coordinate vectors. Idempotence and Hermiticity make P an orthogonal projection, and the complementary hidden projection is constructed as I minus P.

The public seven-condition equivalence includes effective-image descent, interface congruence, absence of carry, factorization, pullback invariance, one-step kernel stability, and the directed cross-block equation.

For self-adjoint T, taking the conjugate transpose of the visible cross block supplies the reverse cross block. The imported commutator identity then makes directed vanishing equivalent to commutation.

The existing sixfold interface theorem and commutator identity are applied directly. Repository and pinned-library searches found no theorem packaging the added matrix clause on this carrier.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/LinearProjectionDescentCriterion.linear_projection_descent_criterion`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](../../ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence.md)
- Dependency: [D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity](../HiddenFlow/ProjectionCommutatorIdentity.md)
