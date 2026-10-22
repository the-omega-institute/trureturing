# Compiled series boundaries

## Abstract

Finite signed Borcherds terms and state derivative for the actual tensor field.

The original tensor carrier is used throughout. The left and right all-integer terms have state-dependent finite support, and the zero-first reduction exposes the signed residue expressions.

**Theorem 1.1 (Left finite support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_left_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_left_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer state-dependent truncation is inherited from the actual state field.

**Theorem 1.2 (Right finite support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_right_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_right_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both nested modes have finite support before the signed difference is formed.

**Theorem 1.3 (Translation as mode minus two).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_translation_as_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_translation_as_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The tensor translation bridge is obtained from covariance, creation, and the tensor vacuum.

**Theorem 1.4 (All-state derivative identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Signed relative-vacuum uniqueness is proved from creation, creativity, covariance and locality; its hypotheses are instantiated with the actual tensor field. The two parity components give the identity on every algebraic state.

Signed residue reconstruction and the all-integer homogeneous and four-component mixed Borcherds equalities hold on the original tensor carrier. These state-field identities do not assert completion of the full conformal field theory or string-theory bridge.

**Theorem 1.5 (Homogeneous residue parity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_residue_mem`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_residue_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every residue mode maps an input of parity s into parity p+q+s. Each pointwise finite sum stays in the corresponding tensor parity submodule.

**Theorem 1.6 (Actual signed residue closure).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_residue_closure`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_residue_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed residue has the mode-product state as its vacuum creation coefficient, is creative and translation covariant, and is relatively local to every homogeneous tensor state. The proved relative-vacuum uniqueness identifies it with the actual state field.

**Theorem 1.7 (Zero-first Borcherds equality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_zero_first`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_zero_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Signed residue closure identifies the iterate coefficients with the two pointwise finite product sums for every integer residue and mode.

**Theorem 1.8 (Forward product support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.firstTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.firstTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

State-dependent truncation makes the first product sequence pointwise finite on each algebraic vector.

**Theorem 1.9 (Reverse product support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.secondTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.secondTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

State-dependent truncation also makes the signed reverse product sequence pointwise finite.

**Theorem 1.10 (Signed product splitting).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.right_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.right_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-support hypotheses justify splitting the signed Borcherds right side into forward and reverse sums.

**Theorem 1.11 (Nonnegative clearing coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.positive_right_products`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.positive_right_products` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative residue degree the two product sums equal the corresponding coefficient of the signed clearing polynomial.

**Theorem 1.12 (All-integer homogeneous Borcherds equality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The discrepancy obeys the Pascal recurrence. Relative locality gives the high-residue seed and actual residue closure gives the zero-first seed. The recurrence proves equality for every integer p,q,r without a global mode cutoff.

**Theorem 1.13 (Explicit four-component equality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.mixed_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.mixed_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two actual parity projections on each state give the even-even, even-odd, odd-even and odd-odd signed equalities. Their four right sides equal the unprojected left side on every algebraic tensor state and vector.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_left_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_right_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.borcherds_zero_first`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.firstTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.mixed_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.positive_right_products`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.right_split`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.secondTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_residue_closure`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_residue_mem`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_translation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorJacobi.stateField_translation_as_mode`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostTensorLocality](LatticeBcGhostTensorLocality.md)
- Dependency: [D5/S3/VertexAlgebra/SuperStateFieldReconstruction](SuperStateFieldReconstruction.md)
