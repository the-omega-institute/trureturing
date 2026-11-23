# Actual Leech orbifold bosonic BRST

## Abstract

The bosonic BRST charge for the actual orbifold is nilpotent and contracts at nonzero energy.

The state carrier is the critical orbifold and hyperbolic lattice matter tensored with the native bc ghost Fock space. E is the total Virasoro zero mode and b₀ is the native zero antighost acting on this carrier.

**Theorem 1.1 (Nilpotence of the original charge).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.Q_squared`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.Q_squared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Q² = 0 on the full tensor product, by the general square anomaly at central charge 26.

**Theorem 1.2 (Nilpotence on each eigenspace).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.differential_squared`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.differential_squared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex eigenvalue μ, the restriction d of Q to the μ-eigenspace of E satisfies d² = 0.

**Theorem 1.3 (Explicit contraction at nonzero energy).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero complex μ, h is the restriction of μ⁻¹b₀ to the μ-eigenspace and d h + h d is the identity there. The zero-mode Ward identity gives Q b₀ + b₀ Q = E.

**Theorem 1.4 (Primitive of a closed nonzero-energy state).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.exact_of_closed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.exact_of_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero complex μ and state x with E x = μx and Q x = 0, the specified primitive satisfies Q(μ⁻¹b₀ x) = x.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.Q_squared`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.contraction`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.differential_squared`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST.exact_of_closed`
- Dependency: [D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCriticalMatter](ActualLeechOrbifoldCriticalMatter.md)
