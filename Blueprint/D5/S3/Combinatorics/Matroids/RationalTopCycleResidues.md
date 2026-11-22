# Rational Top Cycle Residues

## Abstract

Lift residue cycles to rational top cycles.

**Theorem 1.1 (Lift residue cycles to rational top cycles).**

Lean statement: `D5/S3/Combinatorics/Matroids/RationalTopCycleResidues.rational_cycle_residues_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RationalTopCycleResidues.rational_cycle_residues_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite ordered matroid, every coefficient function on its bases with values in Q/Z and zero augmented boundary lifts, in all face coordinates at once, to a rational top cycle. Choose rational coefficients on the internally passive bases and combine the integral cycles normalized there. A residue cycle with zero passive coefficients must vanish: the colexicographically largest nonzero basis has an internally active element, and deleting it leaves a single potentially nonzero term of unit sign in the boundary.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RationalTopCycleResidues.rational_cycle_residues_lift`
- Dependency: [D5/S3/Combinatorics/Matroids/RationalJointCircuitImage](RationalJointCircuitImage.md)
