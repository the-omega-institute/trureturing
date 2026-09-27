# Finite Detection Dark-Block Contraction

## Abstract

The no-click survival operators factor through the dark complement, where one dimension block is uniformly contractive.

**Theorem 1.1 (Dark-complement survival contracts within one dimension block).**

$$\forall d \in \mathbb{N}, X \in \operatorname{Type}, fintype \in \operatorname{Fintype}\left(X\right), Q \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), L \in X \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \left({Q}^{*} \cdot Q + \sum_{x \in X} {L\left(x\right)}^{*} \cdot L\left(x\right) = I_{d} \land d \ne 0\right) \Rightarrow \left(\exists g \in \mathbb{R}, c \in \mathbb{N} \to \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(0 < g \land g \le 1\right) \land \left(\forall N \in \mathbb{N},\; 0 \le c\left(N\right)\right)\right) \land \left(\forall N \in \mathbb{N},\; c\left(N\right) \le 1\right)\right) \land \left(\forall N \in \mathbb{N},\; c\left(N + d\right) \le \left(1 - g\right) \cdot c\left(N\right)\right)\right) \land \left(\forall N \in \mathbb{N},\; \operatorname{darkProjection}\left(Q, L\right) \le {{Q}^{*}}^{N} \cdot {Q}^{N}\right)\right) \land \left(\forall N \in \mathbb{N},\; {{Q}^{*}}^{N} \cdot {Q}^{N} - \operatorname{darkProjection}\left(Q, L\right) = \left(I_{d} - \operatorname{darkProjection}\left(Q, L\right)\right) \cdot {{Q}^{*}}^{N} \cdot {Q}^{N} \cdot \left(I_{d} - \operatorname{darkProjection}\left(Q, L\right)\right)\right)\right) \land 0 \le I_{d} - \operatorname{darkProjection}\left(Q, L\right)\right) \land \left(\forall N \in \mathbb{N},\; {{Q}^{*}}^{N} \cdot {Q}^{N} - \operatorname{darkProjection}\left(Q, L\right) \le \operatorname{smul}\left(c\left(N\right), I_{d} - \operatorname{darkProjection}\left(Q, L\right)\right)\right)\right) \land \left(\forall N \in \mathbb{N},\; \left\lVert {{Q}^{*}}^{N} \cdot {Q}^{N} - \operatorname{darkProjection}\left(Q, L\right) \right\rVert \le c\left(N\right)\right)\right) \land 1 - g = c\left(d\right)\right) \land {{Q}^{*}}^{d} \cdot {Q}^{d} - \operatorname{darkProjection}\left(Q, L\right) \le \operatorname{smul}\left(1 - g, I_{d} - \operatorname{darkProjection}\left(Q, L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FiniteDetectionDarkBlockContraction.dark_block_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be the no-click operator and L_x the finite family of click operators. Their adjoint products sum with Q^* Q to the identity. Write D for the vectors never detected and P for the orthogonal projection onto D.

The squared norms of powers of the restriction of Q to the orthogonal complement of D define coefficients c_N between zero and one. Every survival operator dominates P, and its excess over P factors through the complementary projection, has norm at most c_N, and is bounded by c_N(I-P).

Compactness of the unit sphere in the finite-dimensional dark complement turns pointwise strict decay after d steps into a uniform gap g. Thus one block of survival above P is bounded by (1-g)(I-P).

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FiniteDetectionDarkBlockContraction.dark_block_contraction`
- Dependency: [D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace](../../ObserverMemory/Dynamics/MaximalUnobservableSubspace.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/ResidualKernelInvariance](../../ObserverMemory/Dynamics/ResidualKernelInvariance.md)
- Dependency: [D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace](FiniteDetectionDarkSpace.md)
