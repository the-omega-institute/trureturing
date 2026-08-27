# Robust Frame Bounds

## Abstract

Weighted finite readouts have sharp spectral frame bounds.

**Theorem 1.1 (Weighted readouts have sharp frame bounds).**

$$\begin{gathered}\forall d: \mathbb{N}, \operatorname{NeZero}(d), I: Type, \operatorname{Fintype}(I),\\{}w: I \to NNReal, E: I \to \operatorname{HermitianSpace}(d),\\{}1 < d \Rightarrow\\{}\operatorname{let} A: \operatorname{LinearMap}(\mathbb{R}, \operatorname{traceZeroHermitian}(d), \operatorname{EuclideanSpace}(\mathbb{R}, I)), \operatorname{A}(D)_{i} := \sqrt{w_{i}} \langle D, E_{i}\rangle_{\mathbb{R}},\\{}\alpha := \operatorname{lambdaMin}(A^{*} A), \beta := \operatorname{lambdaMax}(A^{*} A),\\{}\kappa := \frac{\operatorname{sigmaMax}(A)}{\operatorname{sigmaMin}(A)},\\{}(\forall D: \operatorname{traceZeroHermitian}(d), \alpha \left\lVert D \right\rVert^{2} \leq \left\lVert \operatorname{A}(D) \right\rVert^{2} \land \left\lVert \operatorname{A}(D) \right\rVert^{2} \leq \beta \left\lVert D \right\rVert^{2}) \land\\{}(\operatorname{Injective}(A) \iff 0 < \alpha) \land\\{}\kappa = \sqrt{\frac{\beta}{\alpha}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/RobustFrameBounds.robust_observer_frame_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d exceed one and let a finite index type label nonnegative weights and Hermitian effects. The analysis map sends a real trace-zero Hermitian perturbation to its weighted Hilbert--Schmidt effect coordinates.

The lower and upper constants are the least and greatest eigenvalues of the adjoint Gram operator. Expanding in its ordered orthonormal eigenbasis gives both quadratic frame bounds.

The least endpoint is positive exactly when the analysis map is injective. Squared singular values are the Gram eigenvalues, so the singular-value condition ratio is the square root of the endpoint ratio.

The dimension premise excludes d equal to one, whose trace-zero Hermitian carrier has dimension zero and therefore has no least Gram eigenvalue in the source construction.

## References

- Truth anchor: `D5/S3/Observer/Linear/RobustFrameBounds.robust_observer_frame_bounds`
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../../Quantum/Tomography/InformationalCompletenessEquivalence.md)
