# Carrier and reuse

## Abstract

Actual parity grading of full original quotient fields.

Every operation is the existing operation on OriginalCycles and OriginalCohomology. The existing LatticeBcGhostCohomologyModes.parity_decomposition supplies the even-plus-odd decomposition. Tensor parity idempotence, orthogonality, stateField_mem and translation_mem are reused through the actual quotient linear map. These transported helpers are consumed by the signed state-field interface and carry no independent mathematical novelty credit.

**Theorem 1.1 (Descended parity idempotence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural parity label and every quotient state, applying its actual parity projection twice equals applying it once.

**Theorem 1.2 (Descended parity orthogonality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Labels with distinct residues modulo two have zero composite on every quotient state.

**Theorem 1.3 (Parity labels modulo two).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_periodic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Labels with equal residues modulo two give the same actual parity projection on every quotient input.

**Theorem 1.4 (Actual homogeneous cycle representatives).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.homogeneous_representative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.homogeneous_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every parity-fixed quotient state has a representative in the genuine full OriginalCycles whose actual tensor parity is the specified label. Surjectivity first selects a cycle; its actual parity projection preserves its class and lies in the tensor homogeneous submodule.

**Theorem 1.5 (Every integer mode respects the sum of parities).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.product_parity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.product_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary integer mode and two actual parity-fixed quotient states, their genuine bilinear product is fixed by the sum parity. The proof uses homogeneous representatives, product_mk, and the existing tensor mode grading.

**Theorem 1.6 (The actual quotient vacuum is even).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.vacuum_even`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.vacuum_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual tensor vacuum representative has even ghost parity; its existing quotient image is fixed by the even projection.

**Theorem 1.7 (Actual translation preserves homogeneous parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.translation_parity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.translation_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation of any parity-fixed quotient state has the same parity. The existing cycle translation, quotient map and tensor translation_mem establish this statement without replacing the state carrier.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.homogeneous_representative`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_idempotent`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_orthogonal`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.parity_periodic`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.product_parity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.translation_parity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyParity.vacuum_even`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality](LatticeBcGhostCohomologyLocality.md)
