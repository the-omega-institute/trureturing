# Relative reconstruction

## Abstract

Signed vacuum uniqueness for state fields with an explicit parity decomposition.

The coefficient clearing expansion and vacuum recurrence generalize the supplied bc proof to arbitrary complex modules. Creation, creativity, translation vacuum, covariance, parity decomposition and relative signed locality are explicit hypotheses, not a uniqueness endpoint.

**Theorem 1.1 (Vanishing from the vacuum).**

Lean statement: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.relative_vacuum_uniqueness`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.relative_vacuum_uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof first kills all negative vacuum coefficients, then uses the locality clearing polynomial to recover action on homogeneous states. The two supplied parity components exhaust arbitrary inputs. The actual tensor state derivative consumes this result.

**Theorem 1.2 (Nonnegative residue coefficients).**

Lean statement: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.positive_residue_modes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.positive_residue_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed nonnegative residue coefficients are the coefficients of the locality clearing polynomial.

**Theorem 1.3 (Signed nonnegative Dong law).**

Lean statement: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.nonnegative_residue_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.nonnegative_residue_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three pairwise clearing polynomials imply a vector-independent clearing order for the signed residue against the third field.

**Theorem 1.4 (All-integer signed residue locality).**

Lean statement: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.residue_superLocal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.residue_superLocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative residues use the polynomial cancellation law. Negative residues use divided derivatives and signed normal products; their Koszul parities add.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.nonnegative_residue_locality`
- Truth anchor: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.positive_residue_modes`
- Truth anchor: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.relative_vacuum_uniqueness`
- Truth anchor: `D5/S3/VertexAlgebra/SuperStateFieldReconstruction.residue_superLocal`
