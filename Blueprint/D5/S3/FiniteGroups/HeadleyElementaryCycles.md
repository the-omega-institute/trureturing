# Field orbits and the small two-primary leaves

## Abstract

Field orbits and the small two-primary leaves

**Definition 1.1 (Every elementary rank at least two).**

Lean statement: `D5/S3/FiniteGroups/HeadleyElementaryCycles.elementaryCycle`

*Formalization.* `D5/S3/FiniteGroups/HeadleyElementaryCycles.elementaryCycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A primitive unit in the field of cardinality two to the rank acts transitively on its nonzero additive elements. Multiplication by the primitive unit minus one permutes their directed differences, including the closing edge. A basis transports this cycle to the elementary coordinate group; rank three is included.

**Definition 1.2 (The E4 quotient triple).**

Lean statement: `D5/S3/FiniteGroups/HeadleyElementaryCycles.e4RStar`

*Formalization.* `D5/S3/FiniteGroups/HeadleyElementaryCycles.e4RStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successor traverses (1,0), (1,1), (0,1). Its differences permute the same three nonzero elements, and the first plus the third is the second.

**Definition 1.3 (The R-only seven-vertex leaf).**

Lean statement: `D5/S3/FiniteGroups/HeadleyElementaryCycles.c2c4Cycle`

*Formalization.* `D5/S3/FiniteGroups/HeadleyElementaryCycles.c2c4Cycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word is (0,2), (1,3), (0,3), (1,1), (1,0), (1,2), (0,1). Its directed differences are (1,1), (1,0), (1,2), (0,3), (0,2), (1,3), (0,1), including closure. This leaf supplies an R-cycle, with no R-star assertion. These constructions belong to the Headley R-sequenceability induction; no originality claim is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyElementaryCycles.c2c4Cycle`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyElementaryCycles.e4RStar`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyElementaryCycles.elementaryCycle`
- Dependency: [D5/S3/FiniteGroups/HeadleyExtension](HeadleyExtension.md)
