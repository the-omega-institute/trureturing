# Duality Insufficiency

## Abstract

Reciprocal split duality does not force zero drift or a positive invariant metric.

**Theorem 1.1 (Split duality does not select the unitary boundary).**

$$\begin{gathered}\forall \delta, \gamma, P: \mathbb{R},\\{}0 < P \land \delta \neq 0 \Rightarrow\\{}\operatorname{let} a: \mathbb{C} = (\delta + i\gamma) \cdot P; \operatorname{let} u: \mathbb{C} = \operatorname{exp}(a); \operatorname{let} v: \mathbb{C} = \operatorname{exp}(-a); \\{}\operatorname{let} M: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}) = \operatorname{diagonal}({[u, v]}); \operatorname{let} \rho: \mathbb{C} = \frac{1}{2} + \delta + i\gamma; \\{}\operatorname{let} D: \operatorname{Prop} = {\operatorname{xiReading}(1 - \rho) = \operatorname{xiReading}(\rho) \land\\{}\operatorname{det}(M) = 1 \land\\{}qubitX \cdot M \cdot qubitX = M^{-1} \land\\{}u \cdot v = 1 \land\\{}\left\lVert u \right\rVert \neq 1 \land \left\lVert v \right\rVert \neq 1 \land\\{}M^{T} \cdot qubitX \cdot M = qubitX}; \\{}D \land \neg {D \Rightarrow \delta = 0} \land \neg \exists H: \operatorname{Matrix}(\operatorname{Fin}(2), \operatorname{Fin}(2), \mathbb{C}), \operatorname{PosDef}(H) \land M^{*} \cdot H \cdot M = H.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/DualityInsufficiency.duality_insufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two diagonal multipliers are constructed from arbitrary real drift and phase parameters and an arbitrary strictly positive observation period. The branch exchange is the canonical qubitX matrix already owned by the finite-dimensional matrix family.

Reflection, determinant one, reciprocal branch exchange, nonunit multipliers, and preservation of the split bilinear form all hold at nonzero drift. The imported positive-metric selection theorem then rules out every positive definite invariant Hermitian metric.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Algebra/DualityInsufficiency.duality_insufficiency`
- Dependency: [D5/S3/ConceptDynamics/Algebra/PositiveInvariantMetricSelection](PositiveInvariantMetricSelection.md)
- Dependency: [D5/S3/Quantum/FiniteDimensional](../../Quantum/FiniteDimensional.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](../../Zeros/Symmetry/ZetaConjugationCovariance.md)
