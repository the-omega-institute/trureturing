# State-Field Residues and the All-Integer Iterate Law

## Abstract

Unrestricted state fields are closed under every integer residue and satisfy the finite iterate identity.

Let V be the full complex module and let Y be the actual linear state-field map. The hypotheses are primitive creation, creativity, translation covariance and pairwise operator-uniform locality. The construction uses pointwise finite sums on every actual vector, so it does not form an infinite sum in End(V), assume Jacobi or associativity, or replace V by a polynomial Fock carrier.

Primary attribution: Carpi--Codogni, arXiv:2605.26972v1, section 2.1, equation (8), with the standard reconstruction argument. The cited source motivates the mode formula; the declarations below are the native unrestricted-carrier proofs and do not assert Moonshine Conjecture 14.4.

**Theorem 1.1 (Positive residues preserve uniform locality).**

Lean statement: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.residue_nonnegative_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.residue_nonnegative_locality` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For r at least zero, the residue coefficient is the rth finite difference of the actual commutator. The triple discrepancy is killed by the three pairwise locality polynomials; the finite binomial expansion gives an order independent of the input vector. The proof consumes the shift-intertwining helpers.

**Theorem 1.2 (Creative covariant local fields are uniquely reconstructed).**

Lean statement: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.relative_vacuum_uniqueness`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.relative_vacuum_uniqueness` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

A field with zero nonnegative and minus-one vacuum coefficients, translation covariance and locality against every existing Y-state field is zero. The negative vacuum coefficients are obtained by the translation recurrence, and locality at the shifted coefficient isolates each actual mode on each state.

**Theorem 1.3 (Every integer residue is an actual state field).**

Lean statement: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.residue_closure`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.residue_closure` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The residue field is constructed for every integer r. Negative residues are identified with the generic divided-derivative normal-minus-one product, while positive residues use the explicit three-field cancellation. Finite telescoping proves covariance and creation supplies the initial state. Relative vacuum uniqueness then identifies the field with Y of the actual mode product.

**Theorem 1.4 (Finite two-sum iterate identity for all integer modes).**

Lean statement: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.stateField_iterate_of_creation_translation_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.stateField_iterate_of_creation_translation_locality` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For every actual a, b, c and every integers r and n, both binomial mode sums have finite support. Their difference is the n-mode of the actual state field Y(a_r b), with the exact integer Ring.choose coefficients and the factor (-1)^r. This is the unrestricted native iterate prerequisite for later collision arguments; it does not claim a Moonshine realization, equality, or completion of Conjecture 14.4.

## References

- Truth anchor: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.relative_vacuum_uniqueness`
- Truth anchor: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.residue_closure`
- Truth anchor: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.residue_nonnegative_locality`
- Truth anchor: `D5/S3/VertexAlgebra/StateFieldResidueReconstruction.stateField_iterate_of_creation_translation_locality`
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProductLocality](FieldNormalProductLocality.md)
