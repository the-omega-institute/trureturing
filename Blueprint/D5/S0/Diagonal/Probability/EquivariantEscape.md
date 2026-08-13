# Uniform Equivariant Escape Probability

## Abstract

Uniform equivariant listings have the exact transitive escape probability.

**Theorem 1.1 (Transitive uniform equivariant escape probability).**

$$\operatorname{PescEq}\left(f\right) = 1 - \frac{\operatorname{card}\left(\operatorname{Fix}\left(f\right)\right)}{\operatorname{card}\left(Y\right)^{\operatorname{card}\left(\operatorname{StabilizerOrbit}\left(a_{0}\right)\right)}}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Probability/EquivariantEscape.transitive_equivariant_escape_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a transitive group action, choose an address representative a_0. Let omega be the number of stabilizer orbits on addresses, n the cardinality of Y, and k the number of fixed points of f. The canonical stabilizer-orbit coordinates identify all equivariant listings with n^omega parameter choices. Exactly n^omega-k choices escape, so the uniform PMF assigns the escape event probability 1-k/n^omega.

A subgroup G of Sym(A) acts faithfully on A. The Lean theorem is freely more general: it assumes only a group action and transitivity, so it also covers nonfaithful actions without weakening the source claim.

The imported general orbit-product theorem and its regular Z3, regular Z4, and nonregular S3 arithmetic checks retain the source's general-case and redundant-verification clauses.

## References

- Truth anchor: `D5/S0/Diagonal/Probability/EquivariantEscape.transitive_equivariant_escape_probability`
- Dependency: [D5/S0/Diagonal/EquivariantEscape](../EquivariantEscape.md)
