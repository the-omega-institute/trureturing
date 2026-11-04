# Physical Petz error has weighted modular coordinates

## Abstract

Physical Petz error has weighted modular coordinates.

**Definition 1.1 (The supported physical matrix error).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physicalWeightedError`

*Formalization.* `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physicalWeightedError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an actual supported relative-modular model M, put H=sqrt(S), P_R=spectralSupport(R), and E_M(x)=H Psi(spectralX(x)) P_R-sqrt(R). The right support projection is part of the definition; its kernel columns vanish. All matrices and the adjoint Psi belong to the same actual channel and density-state pair. This definition is consumed by all three coordinate estimates below.

**Definition 1.2 (The modular inverse-square-root error).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.modularCoordinateError`

*Formalization.* `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.modularCoordinateError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same model define d_M(x)=A^(-1/2) xi-V x, using cfc(t -> 1/sqrt(t)) on the positive support carrier of A. This coordinate vector is not itself the physical matrix error. At x=B^(-1/2) eta it is the inverse-square-root intertwining error consumed by PetzCoreTraceStability.

**Theorem 1.3 (Each positive coordinate carries a spectral weight).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_positive_coordinate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_positive_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j in the positive S spectrum and i in the positive R spectrum, <v_j,E_M(x)u_i> = -sqrt(s_j/r_i) d_M(x)_(j,i). The model retains input support containment. Consequently the physical error has a spectral weight sqrt(s_j/r_i), rather than an unweighted modular coordinate norm. This identity is consumed by physical_weighted_parseval.

**Theorem 1.4 (Full physical Parseval includes the kernel coordinates).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_weighted_parseval`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_weighted_parseval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coordinate vector x, ||E_M(x)||_HS^2 = sum_(j,i) (s_j/r_i) |d_M(x)_(j,i)|^2 over the positive S and R support indices. Positive-support containment makes the omitted zero-spectrum rows vanish, and P_R makes the omitted kernel columns vanish. The equality concerns the full physical matrix and is consumed by physical_hs_sq_le_coordinate_sq. Singular physical density matrices are included.

**Theorem 1.5 (An actual spectral upper bound controls the physical norm).**

Lean statement: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_hs_sq_le_coordinate_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_hs_sq_le_coordinate_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If s_j/r_i <= L for every positive support pair, then ||E_M(x)||_HS^2 <= L sum_(j,i) |d_M(x)_(j,i)|^2. This theorem states exactly that upper-bound hypothesis; it does not replace the weighted norm by an unweighted one with constant one. PetzCoreTraceStability.petz_core_traceNorm_le_weighted_inverse_sqrt_error consumes the estimate at x=B^(-1/2) eta. These are auxiliary spectral and norm consequences, without an independent novelty claim.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.modularCoordinateError`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physicalWeightedError`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_hs_sq_le_coordinate_sq`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_positive_coordinate`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_weighted_parseval`
- Dependency: [D5/S3/Quantum/Foundation/HilbertSchmidtTraceStability](../Foundation/HilbertSchmidtTraceStability.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSpectralCoordinates](PetzSpectralCoordinates.md)
