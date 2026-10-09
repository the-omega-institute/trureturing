# Finite dominating-set averages

## Abstract

Finite dominating sets have positive family sizes and exact rational average orders.

**Definition 1.1 (Dominating sets).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverage.domSets`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverage.domSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subsets whose closed neighbourhood covers the vertex set.

**Definition 1.2 (Global average).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverage.avd`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverage.avd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the cardinalities divided by the number of dominating sets.

**Definition 1.3 (Local average).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverage.avdAt`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverage.avdAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same mean restricted to sets containing a specified vertex.

**Definition 1.4 (Star-like graphs).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverage.StarLike`

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverage.StarLike` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every vertex is a leaf or a stem with exactly one or two leaf neighbours. This is the definition in Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475.

**Theorem 1.5 (Isomorphism invariance).**

Lean statement: `D5/S3/Combinatorics/Graph/DominatingSetAverage.avd_iso`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverage.avd_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping finite sets along a graph isomorphism gives a cardinality-preserving bijection of the dominating families.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverage.StarLike`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverage.avd`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverage.avdAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverage.avd_iso`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverage.domSets`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](../../ConceptDynamics/GraphColoring/GraphCoverDomination.md)
