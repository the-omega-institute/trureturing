# A quantitative bound on the purity decrease

## Abstract

A lower bound on a strict purity decrease when one Slater orbital is balanced.

**Theorem 1.1 (Purity decrease from a basis of discarded columns).**

Lean statement: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropBound.orderedMarginal_purity_drop_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropBound.orderedMarginal_purity_drop_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose disjoint ordered endpoint pairs on either side of a finite site cut. Compare two complex amplitude assignments with the same normalized endpoint probabilities except that a selected retained pair is balanced in the second. Restrict the alternation matrix to the selected row and the other initially balanced rows, and to discarded columns with both endpoint probabilities positive. Split these columns into a basis and its complement.

When the purity strictly decreases, the decrease is bounded below by the selected squared bias times the product of the other biased retained squared biases times the product of the discarded difference-bit probabilities of one over the basis columns.

A positive summand gives a feasible binary difference that evaluates to one on the selected row and zero on the other balanced rows. Fixing the difference bits outside the basis leaves a residual in the column space, so the basis coefficients give a feasible assignment. Each required basis bit has mass at least its mass for value one. The product bound holds for every assignment outside the basis, whose total mass is one.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/WeightedSlaterPurityDropBound.orderedMarginal_purity_drop_lower_bound`
- Dependency: [D5/S3/Quantum/Fermionic/WeightedSlaterPairCut](WeightedSlaterPairCut.md)
