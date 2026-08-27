# Maximum Factor-Compatible Subdomain

## Abstract

Largest target-consistent fiber blocks give the sharp factor-compatible domain size.

**Theorem 1.1 (Largest target blocks give the exact compatible-domain size).**

$$\forall X \in Type, B \in Type, Y \in Type, C \in X \to B, T \in X \to Y,\; \operatorname{Fintype}\left(X\right) \Rightarrow \left(\left(\forall A \in \operatorname{Finset}\left(X\right),\; \left(\forall x \in X, y \in X,\; \left(\left(x \in A \land y \in A\right) \land C\left(x\right) = C\left(y\right)\right) \Rightarrow T\left(x\right) = T\left(y\right)\right) \Rightarrow \operatorname{card}\left(A\right) \le \operatorname{sum}\left(b, \operatorname{image}\left(C, X\right), \operatorname{max}\left(r, \left\{C\left(r\right) = b \mid r \in X\right\}, \operatorname{card}\left(\left\{C\left(x\right) = b \land T\left(x\right) = T\left(r\right) \mid x \in X\right\}\right)\right)\right)\right) \land \left(\exists A \in \operatorname{Finset}\left(X\right),\; \left(\forall x \in X, y \in X,\; \left(\left(x \in A \land y \in A\right) \land C\left(x\right) = C\left(y\right)\right) \Rightarrow T\left(x\right) = T\left(y\right)\right) \land \operatorname{card}\left(A\right) = \operatorname{sum}\left(b, \operatorname{image}\left(C, X\right), \operatorname{max}\left(r, \left\{C\left(r\right) = b \mid r \in X\right\}, \operatorname{card}\left(\left\{C\left(x\right) = b \land T\left(x\right) = T\left(r\right) \mid x \in X\right\}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TargetRisk/MaximumFactorCompatibleSubdomain.maximum_factor_compatible_subdomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bound is constructed directly from the finite state carrier. For each realized concept value, it counts the largest joint concept-target block and then sums those maxima.

Fiberwise factorization makes every admitted concept fiber fit inside one such block. Conversely, selecting one maximizing target block in every realized concept fiber gives an admitted domain attaining the bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TargetRisk/MaximumFactorCompatibleSubdomain.maximum_factor_compatible_subdomain`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
