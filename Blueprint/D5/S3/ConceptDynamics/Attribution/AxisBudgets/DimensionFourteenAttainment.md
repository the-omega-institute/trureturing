# Attainment with two ordinary rank jumps

## Abstract

An explicit fourteen-coordinate factor attains the lower bound of two ordinary rank jumps.

**Definition 1.1 (Attainment at coordinate zero).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.AttainsTwoJumpsAt640`

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.AttainsTwoJumpsAt640` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take two copies of the subsets of the thirteen free coordinates and mark coordinate zero in dimension fourteen. There exist a Boolean factor and one common Boolean choice for the marked edge. The full-subset loop is absent. The unselected mode allows degree one at both full-subset endpoints, and the selected mode allows degree zero or two at each. Ordinary rows and columns have degree one or three. Every true entry outside the full-subset row is supported on inclusion. The cost is four times the sum of one and the number of true entries from ordinary odd-rank rows to odd-rank columns. It is at most 640. Exactly two true entries in ordinary rows have target rank at least two greater than the source rank.

**Definition 1.2 (The claimed absence of an attaining factor).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.claim`

*Formalization.* `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is no such factor with exactly two ordinary rank jumps.

**Theorem 1.3 (A checked factor refutes the claim).**

Lean statement: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.result`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The claimed absence of an attaining factor is false. The packed row and column lists specify a factor on two copies of the 8192 free-coordinate subsets. The block checks verify the entry agreement, degree conditions, inclusion, and total charge of 159 ordinary entries. Outside the exceptional row, only the entries from mask 15 to 63 and from mask 255 to 1023 can skip a rank. The lower bound already forces two ordinary jumps, so the factor attains it.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.AttainsTwoJumpsAt640`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.claim`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenAttainment.result`
- Dependency: [D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency](../../../../S1/Words/TwoBlockSubstitution/ThueMorseFrequency.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/AxisBudgets/AxisListCertificate](AxisListCertificate.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionFourteenJumps](DimensionFourteenJumps.md)
