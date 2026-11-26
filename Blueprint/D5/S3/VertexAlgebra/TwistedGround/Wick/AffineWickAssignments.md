# Transport of an occurrence word

## Abstract

Wick transport by finite label assignments

**Definition 1.1 (Independent assignments).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments.assign`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments.assign` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every position of a word, sum over the finite native label type and multiply by the corresponding entry of the transport matrix. The empty word evaluates the function on the empty native word.

**Theorem 1.2 (Wick evaluation commutes with transport).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments.wick_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments.wick_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite native label type, transport matrix, complex covariance matrix, mean, and occurrence word, the Wick evaluation with the transported covariance and mean equals the weighted sum of the native Wick evaluations. Induction on word length separates the mean term from the covariance terms. Each covariance term sums the labels at its two paired positions and evaluates the remaining word with those positions erased.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments.assign`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments.wick_transport`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick](AffineOccurrenceWick.md)
