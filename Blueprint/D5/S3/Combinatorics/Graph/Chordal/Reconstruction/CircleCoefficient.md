# Circle gains on finite power paths

## Abstract

Circle-supported gains on finite powers of paths have uniform coefficient one for reconstruction with unrestricted unit-quaternion potentials.

**Theorem 1.1 (Uniform ambient upper bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.powerPath_circle_coefficient_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.powerPath_circle_coefficient_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every finite path order and width, circle-supported gains can be fitted in the full round unit-quaternion group with error at most the triangle-defect budget.

Below half pi, principal triangle angles satisfy the four-face identity and lift to real edge gains. For larger defects, consecutive clique blocks alternate between two orthogonal quaternion lines.

**Theorem 1.2 (Defect of the squared-path example).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.sharpGain_exact_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.sharpGain_exact_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit signed squared-path gains have triangle defect exactly pi divided by four times the length parameter.

Each increasing triangle contains two unit steps and a step of length two. Their signed angles add to one of the two principal angles of the same magnitude.

**Theorem 1.3 (Ambient cycle obstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.sharpGain_ambient_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.sharpGain_ambient_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every full unit-quaternion potential on the squared-path example has a maximum edge error at least the triangle defect times the length parameter divided by one plus that parameter.

The cycle through the even vertices and back through the odd vertices has round holonomy half pi. The product triangle inequality bounds that holonomy by the cycle length times the fitting error.

**Theorem 1.4 (Exact uniform coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.admissible_iff_one_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.admissible_iff_one_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real number is a uniform ambient coefficient for circle gains on finite powers of paths exactly when it is at least one.

The uniform upper construction gives sufficiency. The squared-path lower bounds tend to one as the length parameter grows.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.admissible_iff_one_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.powerPath_circle_coefficient_one`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.sharpGain_ambient_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient.sharpGain_exact_defect`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata](ChordalBanachExactStrata.md)
