# The exhaustive coordinate cases

## Abstract

The exhaustive coordinate cases

**Definition 1.1 (Remove only trivial factors).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateCases.positiveEquiv`

*Formalization.* `D5/S3/FiniteGroups/HeadleyCoordinateCases.positiveEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction to the positive exponents is an additive equivalence because every omitted factor is ZMod 1. No assertion about its underlying prime is needed.

**Definition 1.2 (Elementary coordinates use the field orbit).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateCases.elementaryCoordinates`

*Formalization.* `D5/S3/FiniteGroups/HeadleyCoordinateCases.elementaryCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When every positive exponent is one and two distinct positive entries exist, the positive-coordinate product has rank at least two. The finite-field cycle therefore transfers to the original coordinates.

**Definition 1.3 (The two-factor leaf type).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateCases.twoCoordinatesEquiv`

*Formalization.* `D5/S3/FiniteGroups/HeadleyCoordinateCases.twoCoordinatesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If all exponents except two are zero, evaluation at the two selected entries identifies the entire group with their two cyclic factors.

**Theorem 1.4 (Two positive factors survive the reduction).**

Lean statement: `D5/S3/FiniteGroups/HeadleyCoordinateCases.recursive_pair`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyCoordinateCases.recursive_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Outside the elementary and two-factor minimum-one cases, choose an exponent at least two and another positive exponent. A third positive coordinate, when present, survives untouched. If only two positive coordinates exist, both exponents are at least two and both remain positive after reduction.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateCases.elementaryCoordinates`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateCases.positiveEquiv`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateCases.recursive_pair`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyCoordinateCases.twoCoordinatesEquiv`
- Dependency: [D5/S3/FiniteGroups/HeadleyDoubledCoordinates](HeadleyDoubledCoordinates.md)
- Dependency: [D5/S3/FiniteGroups/HeadleyElementaryCycles](HeadleyElementaryCycles.md)
