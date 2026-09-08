# BalancedHankelSchmidt

## Abstract

Balanced actual Gramians yield the complete Schmidt decomposition of the true infinite Hankel operator.

**Definition 1.1 (normalized Future).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.normalizedFuture`

*Formalization.* `D5/S3/Observer/Hankel/BalancedHankelSchmidt.normalizedFuture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs an isometry by normalizing actual future trajectories with the diagonal Gramian; norm preservation is proved.

**Definition 1.2 (left Isometry).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftIsometry`

*Formalization.* `D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual original-system future trajectories span the finite left Schmidt subspace.

**Definition 1.3 (right Isometry).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightIsometry`

*Formalization.* `D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual dual-system trajectories span the finite right Schmidt subspace.

**Theorem 1.4 (hankel isometric factorization).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_isometric_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_isometric_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves the full l2 operator equals the left isometry composed with the balancing diagonal and the right isometry adjoint.

**Definition 1.5 (left Mode).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftMode`

*Formalization.* `D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the left singular output trajectory associated with a standard state coordinate.

**Definition 1.6 (right Mode).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightMode`

*Formalization.* `D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the right singular input trajectory associated with a standard state coordinate.

**Theorem 1.7 (modes orthonormal).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.modes_orthonormal`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.modes_orthonormal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both trajectory families are orthonormal in their genuine infinite l2 spaces.

**Theorem 1.8 (hankel mode equations).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_mode_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_mode_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves both forward and adjoint singular-vector equations for every positive balancing weight.

**Theorem 1.9 (hankel schmidt expansion).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_schmidt_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_schmidt_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves the complete finite Schmidt expansion for every l2 input, not only finite-support test inputs.

**Theorem 1.10 (hankel kernel iff).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves the nullspace is precisely the orthogonal complement of the constructed right singular modes.

**Theorem 1.11 (nonzero squared singular value).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.nonzero_squared_singular_value`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.nonzero_squared_singular_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proves every nonzero eigenvalue of the actual Hankel adjoint-composition is a squared balancing weight. Repeated weights retain orthogonal modes.

**Theorem 1.12 (constructed core singular values).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_core_singular_values`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_core_singular_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Instantiates the existing finite Gramian singular-value theorem with actual positive square roots. It is supplementary to the separately proved infinite decomposition.

**Theorem 1.13 (constructed hankel schmidt).**

Lean statement: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_hankel_schmidt`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_hankel_schmidt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

End-to-end identification from the original system: constructs actual Gramians and coordinates, proves orthonormal modes, full expansion, kernel characterization and Gramian-product characteristic polynomial. The finite singular multiset is not assumed sorted.

## References

- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_core_singular_values`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_hankel_schmidt`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_isometric_factorization`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_kernel_iff`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_mode_equations`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_schmidt_expansion`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftIsometry`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftMode`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.modes_orthonormal`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.nonzero_squared_singular_value`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.normalizedFuture`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightIsometry`
- Truth anchor: `D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightMode`
- Dependency: [D5/S3/Observer/Hankel/BalancedRealizationTransport](BalancedRealizationTransport.md)
- Dependency: [D5/S3/Observer/Hankel/InfiniteHankelGramian](InfiniteHankelGramian.md)
- Dependency: [D5/S3/Observer/LinearMemory/HankelGramianSingularValues](../LinearMemory/HankelGramianSingularValues.md)
