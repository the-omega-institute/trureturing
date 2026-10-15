# Complete Original Cohomology Coordinates

## Abstract

Explicit representatives and inverse coordinates for the actual exceptional cohomology.

**Theorem 1.1 (No hidden quotient classes).**

$$\operatorname{ker}\left(quotientCoordinates\right) = \operatorname{boundarySubmoduleInCycles}\left(D\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology.quotientCoordinates_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinates retain every sector label except the c0 ground vector and the pure {1,5} ground vector. On cycles the first omitted coordinate is already zero. If all retained coordinates vanish, basis injectivity says the cycle is its pure-pair coefficient times that basis vector, hence a true boundary. Conversely every true boundary has all retained coordinates zero.

**Definition 1.2 (Explicit basis and inverse).**

$$\operatorname{Cohomology}\left(D\right) \equiv \operatorname{FiniteSupport}\left(survivingLabels, Complex\right)$$

*Formalization.* `D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology.cohomologyCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The right inverse extends every finite coefficient function by zero on the omitted labels, then applies the actual sector basis inverse. Its c0 coefficient vanishes, so it is a cycle. This right inverse and the exact kernel identify the true quotient with all finite coefficient functions on the surviving labels.

The surviving representatives are the vacuum ground tensor, the {1,3,5} ground tensor, and for each matter axis its frequency-one excitation with {1} or {1,3}. In particular the triple and the excited c0-containing states are retained; ghost zero modes are not silently discarded.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology.cohomologyCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology.quotientCoordinates_kernel`
- Dependency: [D5/S3/VertexAlgebra/OriginalZeroChargeBrstComplex](OriginalZeroChargeBrstComplex.md)
