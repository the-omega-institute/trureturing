# Single-Kraus Survival Limit

## Abstract

For a complete finite measurement with one no-click operator, the survival effects converge to the orthogonal projection onto the vectors that no click can ever detect.

**Definition 1.1 (The indefinitely undetected subspace).**

$$\forall d: \mathbb{N}, X: \operatorname{Type},\\{}Q: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), L: X \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), \operatorname{darkSpace}(Q, L) = \operatorname{iInter}(n \in \mathbb{N}, x \in X, \operatorname{ker}(L_{x} \cdot Q^{n})).$$

*Formalization.* `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.darkSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dark space consists of the vectors annihilated by every click operator after every finite number of no-click steps.

**Definition 1.2 (The orthogonal dark-space projection).**

$$\forall d: \mathbb{N}, X: \operatorname{Type},\\{}Q: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), L: X \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), \operatorname{darkProjection}(Q, L) = \operatorname{matrix}(\operatorname{starProjection}(\operatorname{darkSpace}(Q, L))).$$

*Formalization.* `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.darkProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dark projection is the matrix of the orthogonal projection onto the dark space.

**Theorem 1.3 (Dark-complement survival contracts geometrically by dimension blocks).**

$$\forall d: \mathbb{N}, X: \operatorname{Type},\\{}Q: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), L: X \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), [\operatorname{Fintype}(X)],\\{}(Q^{*} \cdot Q + \sum_{x \in X} L_{x}^{*} \cdot L_{x} = I_{d} \land d \neq 0) \Rightarrow\\{}\exists g \in \mathbb{R}, c \in \mathbb{N} \to \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(0 < g \land g \le 1\right) \land (\forall N \in \mathbb{N},\; 0 \le \operatorname{c}(N))\right) \land (\forall N \in \mathbb{N},\; \operatorname{c}(N) \le 1)\right) \land (\forall N \in \mathbb{N},\; \operatorname{c}(N + d) \le (1 - g) \cdot \operatorname{c}(N))\right) \land (\forall N \in \mathbb{N},\; \operatorname{darkProjection}(Q, L) \le (Q^{*})^{N} \cdot Q^{N})\right) \land (\forall N \in \mathbb{N},\; (Q^{*})^{N} \cdot Q^{N} - \operatorname{darkProjection}(Q, L) = (I_{d} - \operatorname{darkProjection}(Q, L)) \cdot (Q^{*})^{N} \cdot Q^{N} \cdot (I_{d} - \operatorname{darkProjection}(Q, L)))\right) \land 0 \le (I_{d} - \operatorname{darkProjection}(Q, L))\right) \land (\forall N \in \mathbb{N},\; (Q^{*})^{N} \cdot Q^{N} - \operatorname{darkProjection}(Q, L) \le \operatorname{smul}(\operatorname{c}(N), (I_{d} - \operatorname{darkProjection}(Q, L))))\right) \land (\forall N \in \mathbb{N},\; \left\lVert (Q^{*})^{N} \cdot Q^{N} - \operatorname{darkProjection}(Q, L) \right\rVert \le \operatorname{c}(N))\right) \land 1 - g = \operatorname{c}(d)\right) \land (Q^{*})^{d} \cdot Q^{d} - \operatorname{darkProjection}(Q, L) \le \operatorname{smul}((1 - g), (I_{d} - \operatorname{darkProjection}(Q, L)))\right) \land (\forall n \in \mathbb{N}, k \in \mathbb{N},\; \operatorname{c}(n + k \cdot d) \le (1 - g)^{k})\right) \land (\forall N \in \mathbb{N},\; \operatorname{c}(N) \le (1 - g)^{\operatorname{div}(N, d)})\right) \land (\forall n \in \mathbb{N}, k \in \mathbb{N},\; (Q^{*})^{n + k \cdot d} \cdot Q^{n + k \cdot d} - \operatorname{darkProjection}(Q, L) \le \operatorname{smul}((1 - g)^{k}, (I_{d} - \operatorname{darkProjection}(Q, L))))\right) \land (\forall N \in \mathbb{N},\; (Q^{*})^{N} \cdot Q^{N} - \operatorname{darkProjection}(Q, L) \le \operatorname{smul}((1 - g)^{\operatorname{div}(N, d)}, (I_{d} - \operatorname{darkProjection}(Q, L)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.dark_block_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be the no-click operator and L_x the finite family of click operators. Their adjoint products sum with Q^* Q to the identity. The survival defect above the dark projection is positive, factors through the dark complement, and is controlled by squared norms of restricted powers.

Compactness of the unit sphere in the finite-dimensional dark complement turns strict decay after d steps into a uniform positive gap g. Iterating that block contraction bounds the defect at n+kd by (1-g)^k, and the quotient-remainder decomposition gives the corresponding bound at every N.

**Theorem 1.4 (Survival converges exactly to the dark projection).**

$$\forall d: \mathbb{N}, X: \operatorname{Type},\\{}Q: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), L: X \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), [\operatorname{Fintype}(X)],\\{}Q^{*} \cdot Q + \sum_{x \in X} L_{x}^{*} \cdot L_{x} = I_{d} \Rightarrow\\{}\lim_{N \to \infty} {Q^{*}}^{N} \cdot Q^{N} = \operatorname{darkProjection}(Q, L) \land \forall rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), \lim_{N \to \infty} \operatorname{Tr}(rho \cdot {Q^{*}}^{N} \cdot Q^{N}) = \operatorname{Tr}(rho \cdot \operatorname{darkProjection}(Q, L)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.finite_detection_survival_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q be the no-click operator and let the finite family L_x contain the click operators. Assume that their adjoint products sum with Q^* Q to the identity. The dark space is invariant under Q. On it, Q^*Q is the identity, and finite dimensionality makes the restriction of Q surjective. Consequently the orthogonal complement of the dark space is also invariant under Q.

The dimension-step survival defect has the dark space as its kernel. Positivity therefore makes the dimension-step restriction a strict contraction on the orthogonal complement. Compactness of its unit sphere upgrades pointwise strictness to a uniform contraction, whose powers decay geometrically.

Survival is the identity on the dark space and tends to zero on its orthogonal complement. Hence the survival matrices converge to the orthogonal dark-space projection. Multiplication by any matrix rho followed by the trace is continuous, which gives the trace limit. Dimension zero is included.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.darkProjection`
- Truth anchor: `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.darkSpace`
- Truth anchor: `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.dark_block_contraction`
- Truth anchor: `D5/S3/Quantum/Measurement/FiniteDetectionSurvivalLimit.finite_detection_survival_limit`
- Dependency: [D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace](../../ObserverMemory/Dynamics/MaximalUnobservableSubspace.md)
- Dependency: [D5/S3/ObserverMemory/Dynamics/ResidualKernelInvariance](../../ObserverMemory/Dynamics/ResidualKernelInvariance.md)
- Dependency: [D5/S3/Quantum/Measurement/FiniteDetectionDarkSpace](FiniteDetectionDarkSpace.md)
