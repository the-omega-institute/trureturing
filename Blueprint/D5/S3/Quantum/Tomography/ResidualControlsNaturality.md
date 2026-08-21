# Residual Control of Visible Compression

## Abstract

Orthogonal residual norms control visible compression defects.

**Definition 1.1 (Centered density coordinate).**

$$\forall d, \rho: \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\\{}\operatorname{Density}\left(\rho\right) \Rightarrow \operatorname{densityCoordinate}\left(\rho\right) = \rho - \frac{1}{d} I \in \operatorname{HermitianTraceZero}\left(d\right).$$

*Formalization.* `D5/S3/Quantum/Tomography/ResidualControlsNaturality.densityCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive semidefinite trace-one matrix is centered at the maximally mixed matrix. Hermiticity and trace normalization place the result in the canonical real trace-zero Hermitian carrier.

**Definition 1.2 (Visible compressed dynamics).**

$$\forall d, S: \operatorname{Submodule}\left(\mathbb{R}, \operatorname{HermitianTraceZero}\left(d\right)\right),\\{}F: \operatorname{HermitianTraceZero}\left(d\right) \to \operatorname{HermitianTraceZero}\left(d\right), X: \operatorname{HermitianTraceZero}\left(d\right),\\{}\operatorname{visibleDynamics}\left(S, F\right)(X) = P_{S}(F(X)).$$

*Formalization.* `D5/S3/Quantum/Tomography/ResidualControlsNaturality.visibleDynamics` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The visible dynamics is constructed from the ambient map and the named orthogonal projection: apply the ambient dynamics, then project its output back to the visible subspace.

**Theorem 1.3 (Orthogonal residual controls the visible compression defect).**

$$\begin{gathered}\forall d, \rho: \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\\{}S: \operatorname{Submodule}\left(\mathbb{R}, \operatorname{HermitianTraceZero}\left(d\right)\right), F: \operatorname{HermitianTraceZero}\left(d\right) \to \operatorname{HermitianTraceZero}\left(d\right),\\{}L: \operatorname{NNReal}, X: \operatorname{HermitianTraceZero}\left(d\right),\\{}\operatorname{Density}\left(\rho\right) \land \operatorname{IsClosed}\left(S\right) \land \operatorname{LipschitzWith}\left(L, F\right) \Rightarrow\\{}\operatorname{naturalityDefect}\left(P_{S}, P_{S}, F, \operatorname{visibleDynamics}\left(S, F\right), X\right) \leq L \left\lVert P_{S^{\perp}}(X) \right\rVert \land\\{}\operatorname{naturalityDefect}\left(P_{S}, P_{S}, F, \operatorname{visibleDynamics}\left(S, F\right), \operatorname{densityCoordinate}\left(\rho\right)\right) \leq L \sqrt{\operatorname{residualMass}\left(S, \operatorname{densityCoordinate}\left(\rho\right)\right)}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/ResidualControlsNaturality.residual_controls_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a closed subspace of the real trace-zero Hermitian carrier, let F be L-Lipschitz, and let its visible dynamics be the orthogonal compression constructed above.

The public statement contains both source clauses. For every named coordinate X, the compression defect is at most L times the norm of its orthogonal residual. For the centered density coordinate, the same defect is at most L times the square root of the canonical residual mass.

Mathlib's exact nonexpansiveness theorem for orthogonal projection is composed with the Lipschitz bound for F. Its orthogonal-complement identity identifies the input distance, and the real square-root identity converts the squared residual mass back to its norm.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/ResidualControlsNaturality.densityCoordinate`
- Truth anchor: `D5/S3/Quantum/Tomography/ResidualControlsNaturality.residual_controls_naturality`
- Truth anchor: `D5/S3/Quantum/Tomography/ResidualControlsNaturality.visibleDynamics`
- Dependency: [D5/S0/Diagonal/Naturality/NaturalityDefectComposition](../../../S0/Diagonal/Naturality/NaturalityDefectComposition.md)
- Dependency: [D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence](../Fibers/TraceZeroReadoutOrthogonalEquivalence.md)
- Dependency: [D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras](ComplementaryContextProbabilityPythagoras.md)
