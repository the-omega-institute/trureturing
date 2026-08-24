# Constructive Diagonal Escape

## Abstract

The canonical twisted diagonal escapes every supplied catalog.

**Theorem 1.1 (The canonical diagonal escapes its catalog).**

$$\forall A, Y: \operatorname{Type},\\{}g: A \to \left(A \to Y\right), tau: Y \to Y,\\{}(\forall y: Y, \operatorname{tau}\left(y\right) \neq y) \Rightarrow\\{}\neg (\operatorname{diagonal}\left(tau, g\right) \in \operatorname{range}\left(g\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/ConstructiveDiagonalEscape.constructive_diagonal_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The address type, value type, catalog, and twist are independent source primitives. The escaped function is the established canonical diagonal, sending a to the twist of g(a)(a).

When the twist has no fixed point, this diagonal cannot equal any catalog row. Equality with row g(a) would make g(a)(a) a fixed point after evaluation at a.

The repository contains the exact arbitrary-carrier range theorem, so the Lean proof imports and applies it directly. Pinned Mathlib has related surjectivity and Cantor results but no thinner full-statement match.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/ConstructiveDiagonalEscape.constructive_diagonal_escape`
- Dependency: [D5/S0/Diagonal/Naturality/RelativeDiagonalEscape](../../../S0/Diagonal/Naturality/RelativeDiagonalEscape.md)
