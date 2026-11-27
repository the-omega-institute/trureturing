# Equality in the purity drop of an ordered Slater marginal

## Abstract

Equality in the column-basis lower bound for a strict Slater purity drop.

**Theorem 1.1 (Equality for a given column basis).**

Lean statement: `D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropEquality.orderedMarginal_purity_drop_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropEquality.orderedMarginal_purity_drop_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Balance one biased retained pair and keep every other endpoint probability. Under strict purity decrease, restrict the alternation matrix to the active discarded pairs. Choose a basis of the columns on the selected row and the other balanced retained rows. Equality in the pivot-column bound holds exactly when the unit row for every nonbalanced basis column and the restricted row for every other nondeterministic biased retained pair differ from the selected row by an element of the span of the other balanced rows. The exact Gram-square trace difference is a weighted sum on the feasible binary fiber. Each free assignment has strictly positive mass, so any strict increase in a factor yields strict excess over the bound.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropEquality.orderedMarginal_purity_drop_eq_iff`
- Dependency: [D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropBound](WeightedSlaterPurityDropBound.md)
- Dependency: [D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropEquality](WeightedSlaterPurityDropEquality.md)
