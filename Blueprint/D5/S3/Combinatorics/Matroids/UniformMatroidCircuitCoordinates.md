# Uniform Matroid Circuit Coordinates

## Abstract

The two equations for the uniform core.

**Theorem 1.1 (The two equations for the uniform core).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates.form_mem_weighted_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates.form_mem_weighted_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a matroid on the full finite ground whose bases are all subsets of the stated positive size, let a take the value one on each vector of the chosen basis. The form coordinates, extended by zero off the matroid bases, belong to the weighted residue group exactly when covector multiplication by a and insertion of the basis vector sum weighted by class sizes both vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformMatroidCircuitCoordinates.form_mem_weighted_iff`
- Dependency: [D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction](ParallelCircuitObstruction.md)
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms](UniformCircuitResidueForms.md)
