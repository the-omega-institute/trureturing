# Abstract finite abelian two-groups in coordinates

## Abstract

Abstract finite abelian two-groups in coordinates

**Theorem 1.1 (Discharge the coordinate presentation).**

Lean statement: `D5/S3/FiniteGroups/HeadleyTwoGroupNormalization.coordinate_presentation`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyTwoGroupNormalization.coordinate_presentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite abelian structure theorem supplies prime-power cyclic factors. A factor with positive exponent has its prime dividing the group order, so the two-group cardinality forces that prime to be two. Zero exponents remain trivial independently of their prime. Reindexing gives coordinates indexed by a finite ordinal. If fewer than two exponents were positive, evaluation would inject the group into one cyclic factor, or the whole group would be trivial; either case contradicts noncyclicity.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyTwoGroupNormalization.coordinate_presentation`
- Dependency: [D5/S3/FiniteGroups/HeadleyCoordinateKernel](HeadleyCoordinateKernel.md)
