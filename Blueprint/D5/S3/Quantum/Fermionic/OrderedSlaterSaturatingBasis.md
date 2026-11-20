# Existence of an attaining column basis

## Abstract

A rank test for attaining the ordered Slater purity-drop bound.

**Theorem 1.1 (An attaining basis exists exactly at full eligible rank).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterSaturatingBasis.orderedMarginal_exists_saturating_basis_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterSaturatingBasis.orderedMarginal_exists_saturating_basis_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Balance one retained pair while holding the discarded weights fixed, and assume the ordinary marginal purity strictly decreases. Restrict the alternation matrix to the selected and other balanced retained rows and the nondeterministic discarded columns. The target has a one on the selected row and zero on all other rows. An attaining basis exists exactly when the retained-row coset condition holds and the rank of the balanced discarded columns, plus the number of nonbalanced discarded columns whose deletion excludes the target from the span, equals the full column rank. The deletion test detects precisely the coordinates forced to be one on the feasible fiber. Every such nonbalanced column adds one dimension to the span of the balanced columns and the other eligible columns. One attaining basis consists of a basis of the balanced discarded columns together with all the indispensable nonbalanced columns.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterSaturatingBasis.orderedMarginal_exists_saturating_basis_iff`
- Dependency: [D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropEquality](OrderedSlaterPurityDropEquality.md)
