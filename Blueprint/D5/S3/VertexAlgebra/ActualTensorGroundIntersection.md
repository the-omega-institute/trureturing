# Actual Tensor Ground Intersection

## Abstract

Nonnegative actual currents force every nonzero invariant tensor submodule to meet the selected finite ground.

Let D be the existing integral even lattice datum and let hu : IsUnit D.G.det assert that the integral Gram determinant is a unit. The existing actual twisted finite ground representation is selected from D and hu. The tensor carrier is the native oscillator polynomial algebra tensor the selected ground function space. No positivity, rank restriction, simplicity assumption or global state-field law is added.

**Theorem 1.1 (A nonzero current-stable tensor submodule contains a nonzero ground tensor).**

Lean statement: `D5/S3/VertexAlgebra/ActualTensorGroundIntersection.nonzero_current_stable_submodule_meets_ground`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ActualTensorGroundIntersection.nonzero_current_stable_submodule_meets_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero submodule S stable under every nonnegative actual current, the proof takes a nonzero element whose maximum total degree over all finite ground coordinates is least. If a positive partial acts nontrivially, the same maximum degree strictly decreases, so every partial vanishes on the minimizer. The pinned polynomial rigidity lemma then makes every coordinate constant, yielding a nonzero tensor 1 tensor g in S.

The current-to-partial step uses the row H x.1 of the mapped inverse Gram matrix, with H times the complex Gram matrix equal to the identity. At frequency x.2 the actual current is the nonzero scalar frequency(x.2) times the corresponding weighted partial, so submodule closure transports to each partial. The argument is valid for rank zero and indefinite forms wherever the existing actual ground supplier is available; it makes no claim about coefficient irreducibility, a full VOA, fusion, string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ActualTensorGroundIntersection.nonzero_current_stable_submodule_meets_ground`
- Dependency: [D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity](../Quantum/Algebra/ConditionalPolynomialRigidity.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualAnnihilation](LatticeActualAnnihilation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockTensorFields](LatticeHalfFockTensorFields.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraCurrents](LatticeSugawaraCurrents.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](LatticeTwistedGroundRealization.md)
