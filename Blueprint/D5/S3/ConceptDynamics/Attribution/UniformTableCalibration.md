# Equal-weight seeds at the optimal subgroup-fixed mass

## Abstract

A determinant bound for optimal uniform calibrations of rational finite kernels.

**Theorem 1.1 (A nonsingular orbit minor gives an optimal uniform calibration).**

$$\exists q, r, \operatorname{Injective}(r) \land \operatorname{PositiveMinorBudget}(A, m, q, r, N) \land (\exists U, f, \operatorname{Cardinality}(U, N) \land \operatorname{UniformCalibration}(U, f, N) \land \operatorname{TableWeights}(U, f, N, q) \land \operatorname{Optimal}(U, f, N))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/UniformTableCalibration.uniform_kernel_optimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group G act on finite types X and Y, and fix a subgroup H. The kernel P is nonnegative, row normalized, and G-covariant. The positive integer m clears its denominators, with m times each entry specified by an integer z. X and Y may be empty.

The matrix A has one column for each G-orbit of tables from X to Y. A table is translated by acting on its output and inversely translating its input. The normalization row counts all tables in the orbit. The row indexed by a cell (x,y) counts the orbit's tables that take x to y.

The theorem gives a real weight function q on the orbits and an injective map r from its positive support to the rows of A. The square submatrix B uses those rows and the supported columns. The positive number N equals m times the absolute determinant of B. The seed type U carries a G-action and has cardinality N.

UniformCalibration means that evaluation through f gives marginals P with weight 1/N on every seed, and f is pointwise G-equivariant. TableWeights means that the induced table law assigns each table its orbit's weight q. Optimal means that every finite G-set of seeds, with nonnegative invariant weights summing to one and equivariant readout with the same marginals, has H-fixed mass at most the H-fixed mass of the uniform law on U. The seed type U is in the maximum of the input and output universes. The comparison seed type ranges over an independent universe.

An optimizer with minimum positive support has independent columns. A null direction, oriented to preserve or improve the objective, would otherwise remove a positive coordinate. The adjugate clears denominators on the resulting square minor. Each table then gets an integer number of copies, with the action preserving the copy number.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/UniformTableCalibration.uniform_kernel_optimum`
- Dependency: [D5/S3/Combinatorics/Matroids/LinearRado](../../Combinatorics/Matroids/LinearRado.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/TableOrbitWeights](TableOrbitWeights.md)
