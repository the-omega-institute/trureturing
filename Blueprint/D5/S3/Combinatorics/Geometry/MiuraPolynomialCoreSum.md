# The actual-core run-vector polynomial

## Abstract

A finite rational candidate from individual residual cores.

**Definition 1.1 (An individual residual core).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.CoreState`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.CoreState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each state is a normalized height function with the exact specified minimum and maximum counts, the common physical-side exclusion, at least two cells per axis, no adjacent frozen pair on either axis, and at least one frozen run on each axis.

**Definition 1.2 (The finite family retains every actual core).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.Core`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.Core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Dimensions are natural values below 2(a+b). The dependent family includes every individual core function at those dimensions. Finiteness follows from the finite normalized residual classes on each bounded rectangle.

**Definition 1.3 (Occupied rows).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.rowOccupied`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.rowOccupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count actual rows containing at least one strict minimum or maximum by applying occupied-column counting to the transpose.

**Definition 1.4 (Occupied columns).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.colOccupied`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.colOccupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count actual columns containing at least one strict minimum or maximum.

**Definition 1.5 (Actual frozen row runs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.rowRuns`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.rowRuns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count maximal frozen runs on the transposed column axis.

**Definition 1.6 (Actual frozen column runs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.colRuns`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.colRuns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count maximal frozen runs on the column axis.

**Definition 1.7 (One finite rational polynomial).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.corePolynomial`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.corePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the two-variable positive-run polynomial over the finite family of individual actual residual cores. The sum is independent of the later evaluation dimensions.

**Theorem 1.8 (Exact evaluation of the core-indexed vector sum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.core_polynomial_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.core_polynomial_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For both dimensions at least 2(a+b)-1, evaluation equals the finite sum, over every individual core, of the cardinalities of its positive row-run and column-run vector products. Each total is the corresponding dimension minus the actual occupied-line count. The occupied-line and frozen-run bounds on each actual core prove that all positive-vector parameters are feasible throughout this region. Equality of this vector sum with the residual height-function count requires a canonical-core and expansion-fiber bijection.

**Theorem 1.9 (The strict total degree bound on these same actual cores).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.core_polynomial_degree_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.core_polynomial_degree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a+b at least five, the total degree of this same core polynomial is at most a+b-3. The active-column run definitions are identified with the actual geometric row-run starts after transposition. Positive runs give an unoccupied row on each axis, so the strict residual geometry bound applies to every member of the existing Core family. Each summand has degree at most its two run counts minus two; the finite sum preserves the uniform bound. Equality of its evaluations with residualCount still requires the actual reconstruction and counting bridge.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.Core`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.CoreState`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.colOccupied`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.colRuns`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.corePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.core_polynomial_degree_le`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.core_polynomial_eval`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.rowOccupied`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPolynomialCoreSum.rowRuns`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreNormal](MiuraCoreNormal.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreTranspose](MiuraCoreTranspose.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualityClassification](MiuraEqualityClassification.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraPolynomialRuns](MiuraPolynomialRuns.md)
