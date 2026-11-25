# Actual Leech orbifold norm-two BRST shell

## Abstract

The actual norm-two absolute shell has two coordinates and the relative shell is a line.

The momentum p = (1, 1) lies in the standalone hyperbolic plane. The ground states ψ and ψ₁₃ use the orbifold vacuum and the plane state eᵖ, with ghost occupations {1} and {1, 3} respectively. The coefficients ρ and σ read these states in the fixed sector.

**Theorem 1.1 (Absolute shell).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.mem_absoluteShell_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.mem_absoluteShell_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A state x has momentum p and zero total energy exactly when x = ρ(x)ψ + σ(x)ψ₁₃. The positive twisted weight excludes the entire twisted sector.

**Theorem 1.2 (Fixed points of the projector).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.absoluteProjection_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.absoluteProjection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projector P defined by those two coefficients fixes exactly the absolute shell.

**Theorem 1.3 (Projector identities).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.absoluteProjection_actions`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.absoluteProjection_actions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the full state space P² = P, EP = PE = 0, and PΠₚ = P, where E is the total Virasoro zero mode and Πₚ selects momentum p.

**Theorem 1.4 (Zero antighost coordinate).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.rho_b0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.rho_b0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every state x in the full tensor product, ρ(b₀ x) = −σ(x).

**Theorem 1.5 (Relative shell and charge).**

Lean statement: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.normTwo_relative_shell`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.normTwo_relative_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The intersection C of the absolute shell with the kernel of b₀ is the complex span of ψ. The native ghost number satisfies Nψ = ψ and the actual BRST charge Q vanishes on C.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.absoluteProjection_actions`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.absoluteProjection_eq`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.mem_absoluteShell_iff`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.normTwo_relative_shell`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwo.rho_b0`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy](../../Quantum/Fermionic/BcGhostRelativeEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldBRST](ActualLeechOrbifoldBRST.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace](../LatticeHalfFockGradedTrace.md)
