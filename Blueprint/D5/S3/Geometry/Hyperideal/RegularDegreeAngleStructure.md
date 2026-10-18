# Degree-normalized strict angle structure

## Abstract

Degree-normalized angles give exact global edge sums and a strict local vertex bound.

For a finite paired tetrahedral family, degree(q,e) is the number of actual edge occurrences in the global edge class e, and regularAngle(q,o) is 2*pi divided by the degree of the global edge containing occurrence o.

**Theorem 1.1 (Minimum degree eight gives a strict angle structure).**

Lean statement: `D5/S3/Geometry/Hyperideal/RegularDegreeAngleStructure.regular_degree_angle_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/RegularDegreeAngleStructure.regular_degree_angle_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every actual global edge has degree at least eight. Then every regularAngle is positive, the M sum over every global edge is exactly 2*pi, and every local Q sum is at most 3*pi/4 and therefore strictly less than pi.

The local estimate uses the six tetrahedral edge slots and the fact that at most three slots meet a local vertex; each nonzero contribution is at most pi/4. The theorem concerns the angle structure supplied by the actual pairing. It does not construct common edge lengths, prove a global gluing, establish a general geometric realization, or settle later degeneracy and volume questions.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/RegularDegreeAngleStructure.regular_degree_angle_structure`
- Dependency: [D5/S3/Geometry/Hyperideal/ActualCornerTransport](ActualCornerTransport.md)
