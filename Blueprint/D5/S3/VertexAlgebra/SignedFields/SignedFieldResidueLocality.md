# Signed all-integer residue calculus

## Abstract

Signed all-integer residue calculus

The finite-support constructions and residue telescope retain the Scott Carnahan vertexAlg Apache-2.0 attribution of their existing suppliers. The signed proof calculations adapt the actual bc ghost supplier to arbitrary complex modules, while reusing the existing generic PairSpace cancellation kernel and delta-binomial identity. This is classical Dong locality and creative reconstruction, with no literature novelty claim.

**Theorem 1.1 (Dong locality for every integer residue).**

Lean statement: `D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary fields and independent AB,AC,BC signs x,y,z, every integer signed residue of A and B is local with C with sign yz. Nonnegative residues are boundaries of shifted signed triple pairs. Residue degree -d-1 is the signed normal product of the degree d divided derivative of A and B. Each coefficient sum has finite support after application to a vector.

**Theorem 1.2 (Original translation passes through the residue).**

Lean statement: `D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both input fields are covariant under the same endomorphism T, every signed integer residue is covariant under that T. Integer-binomial recurrence and vectorwise finite telescopes justify all reindexing and sum exchanges.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_locality`
- Truth anchor: `D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueLocality.residue_translation`
- Dependency: [D5/S3/VertexAlgebra/BinomialKernelDelta](../BinomialKernelDelta.md)
- Dependency: [D5/S3/VertexAlgebra/SignedFields/SignedFieldNormalProductLocality](SignedFieldNormalProductLocality.md)
- Dependency: [D5/S3/VertexAlgebra/StateFieldResidueReconstruction](../StateFieldResidueReconstruction.md)
