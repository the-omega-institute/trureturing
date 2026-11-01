# Cyclic Ground Orbit Fixed Vectors

## Abstract

Phase-filtered charged-ground orbit vectors for an actual finite-order cyclic lattice lift.

For an actual lattice isometry g of finite order, CyclicIsometryLift supplies a sign-character correction on the existing Carrier. The phase-filtered charged-ground orbit is the finite sum of the corrected operator powers applied to the literal norm-four ground vector. Because the corrected operator has the stated period, the geometric-sum identity makes this vector fixed.

**Theorem 1.1 (Actual phase-filtered norm-four orbit fixed vector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitBasis.actual_normFour_phase_filtered_orbit_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitBasis.actual_normFour_phase_filtered_orbit_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice datum D, bilinear-preserving additive isometry g, positive period m and periodicity proof, there exists a charge character chi such that the complete m-term corrected orbit sum of every actual norm-four charge ground vector belongs to the corrected fixed submodule. The theorem is an actual Carrier statement and does not assert orbit independence or a shell cardinality.

The proof is a finite geometric telescoping identity on the existing actual Carrier. The cyclic lift theorem supplies the correction and its exact m-th power identity; no replacement coordinate module, enumeration, positivity premise or numerical shell count is introduced.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/CyclicGroundOrbitBasis.actual_normFour_phase_filtered_orbit_fixed`
- Dependency: [D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift](CyclicIsometryLift.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/RootlessLowGrades](RootlessLowGrades.md)
