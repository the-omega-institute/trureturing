# A scalar endpoint slice for the first-slot cosine

## Abstract

The first-slot cosine on the Section 68 scalar slice is not constant at its endpoint.

**Definition 1.1 (First-slot cosine along the scalar slice).**

Lean statement: `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.endpointSlice`

*Formalization.* `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.endpointSlice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local edge order is (12,13,14,34,24,23). For a real parameter epsilon, endpointSlice(epsilon) is the original first-slot cosine at the six coordinates (2,2,2,17-epsilon,2,2).

**Definition 1.2 (Constancy at the endpoint value).**

Lean statement: `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.claim`

*Formalization.* `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim says that every epsilon in the closed interval [0,1] has first-slot cosine equal to -1 along this slice.

**Theorem 1.3 (The scalar slice leaves the endpoint value).**

Lean statement: `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At epsilon = 1/2, direct substitution into the two radicands and the numerator gives denominator 27 and cosine -17/18. This is different from -1, so the universal constancy claim is false. The result concerns this scalar cosine slice only; it does not assert an inverse-cosine regularity theorem or a global flow statement.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.claim`
- Truth anchor: `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.endpointSlice`
- Truth anchor: `D5/S3/Geometry/Hyperideal/AngleExtensionSlice.result`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
