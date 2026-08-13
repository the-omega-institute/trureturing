# Unique Golden-Power Coordinates

## Abstract

The second and third golden powers have unique nonnegative coordinates.

**Theorem 1.1 (The second and third golden powers have unique coordinates).**

$$\forall a,b,c,d \in \mathbb{N},\ a \varphi^{2} + b \varphi^{3} = c \varphi^{2} + d \varphi^{3} \Rightarrow a=c \land b=d.$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/GoldenPowerCoordinates.golden_power_coordinates_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the two real power combinations is transported to the repository's injective real embedding of integral golden coordinates. The two carrier coordinates then determine both natural coefficients.

The proof is a thin corollary of the existing embedding injectivity theorem, whose kernel argument uses Mathlib's irrationality of the golden ratio.

This is an honest partial closure of only the leading uniqueness clause in source theorem 6.38. The bivariate power series, factorization, inversion, coefficient table, truncation audit, and all claims through total degree sixteen remain unresolved.

## References

- Truth anchor: `D5/S1/Eigenstructure/GoldenPowerCoordinates.golden_power_coordinates_unique`
- Dependency: [D5/S1/Scale/Embedding](../Scale/Embedding.md)
