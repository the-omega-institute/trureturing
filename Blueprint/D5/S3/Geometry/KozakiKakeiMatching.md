# Even frieze matrices and alternating matchings

## Abstract

The even-frieze equation compares two literal determinant products on the full space of rectangular matrices.

**Definition 1.1 (Coefficient field).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.K`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficients are complex rational functions in one indeterminate.

**Definition 1.2 (Column labels).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.Col`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.Col` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column set is Fin (2m), indexed from zero.

**Definition 1.3 (Matrix carrier).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.Chart`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.Chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier consists of every matrix with two rows and 2m columns over the given ring.

**Definition 1.4 (First column).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.first`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.first` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first column has index zero.

**Definition 1.5 (Second column).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.second`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.second` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second column has index one.

**Definition 1.6 (Third column).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.third`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.third` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third column has index two.

**Definition 1.7 (Last column).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.last`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.last` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The last column has index 2m − 1.

**Definition 1.8 (Odd matching endpoints).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.oddVertex`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.oddVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At edge index e the ordered endpoints have indices 2e and 2e + 1.

**Definition 1.9 (Even matching endpoints).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.evenVertex`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.evenVertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Edge zero is ordered from the first column to the last. At positive edge index e the ordered endpoints have indices 2e − 1 and 2e.

**Definition 1.10 (Odd matching).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.oddMatching`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.oddMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every column occurs exactly once among the ordered odd edges.

**Definition 1.11 (Even matching).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.evenMatching`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.evenMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every column occurs exactly once among the even edges, including the ordered closing edge.

**Definition 1.12 (Oriented minor).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.minor`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.minor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordered minor is the upper entry of the first column times the lower entry of the second minus the lower entry of the first times the upper entry of the second.

**Definition 1.13 (Admissible matrices).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.Admissible`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every ordered pair of distinct columns has a nonzero minor. This is the nonvanishing condition for all two-column minors.

**Definition 1.14 (Column reordering).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.reorder`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.reorder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column at index i of the reordered matrix is the original column at index σ(i).

**Definition 1.15 (Odd determinant product).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.oddProduct`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.oddProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In one-based notation the factors are D(1,2), D(3,4), through D(2m−1,2m).

**Definition 1.16 (Even determinant product).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.evenProduct`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.evenProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In one-based notation the factors are D(2,3), D(4,5), through D(2m−2,2m−1), and D(1,2m).

**Definition 1.17 (Preservation on all admissible matrices).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.PreservesLevel`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.PreservesLevel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A permutation preserves the level when equality of the two literal products implies equality after reordering for every admissible matrix over the complex rational function field.

**Definition 1.18 (Ordered normalization).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.Normalized`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.Normalized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A matrix is admissible, its first three columns are (0,−1), (1,0), and (1,1), and every consecutive minor and the ordered closing minor D(1,2m) equals one.

**Definition 1.19 (Matrix equivalence).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.MatEquivalent`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.MatEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two matrices are equivalent when one is obtained from the other by invertible left multiplication and an invertible diagonal matrix acting on the right.

**Definition 1.20 (Allowable permutations).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.Allowable`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.Allowable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every normalized input, reordering by the permutation has exactly one matrix-equivalent normalized representative.

**Definition 1.21 (Dihedral permutations).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.Dihedral`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.Dihedral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For some column a, the permutation sends every column i to a+i or sends every column i to a−i, with arithmetic modulo 2m.

**Definition 1.22 (Affine matrices).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.affine`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.affine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first row is all ones and the second row contains the given coordinates.

**Theorem 1.23 (Affine minor).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.minor_affine`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatching.minor_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered minor at i and j is the coordinate at j minus the coordinate at i.

**Definition 1.24 (Polynomial difference).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.diff`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.diff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The oriented linear factor is the variable at j minus the variable at i.

**Definition 1.25 (Oriented matching polynomial).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.matchingPolynomial`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.matchingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply one oriented linear factor for each ordered pair of the matching.

**Definition 1.26 (Signed level polynomial).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.F`

*Formalization.* `D5/S3/Geometry/KozakiKakeiMatching.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The even matching polynomial minus the odd matching polynomial is the affine form of the level equation.

**Theorem 1.27 (Evaluation of a matching product).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.eval_matchingPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatching.eval_matchingPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the matching polynomial multiplies the oriented coordinate differences.

**Theorem 1.28 (The affine level equation).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.eval_F`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatching.eval_F` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial evaluates to the even determinant product minus the odd product of the affine matrix.

**Theorem 1.29 (Admissible constant matrices).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.affine_constants_admissible`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatching.affine_constants_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injective complex coordinates give a matrix whose minors stay nonzero under the inclusion into rational functions.

**Theorem 1.30 (Transfer to the affine locus).**

Lean statement: `D5/S3/Geometry/KozakiKakeiMatching.constant_matrix_implication`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiMatching.constant_matrix_implication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A permutation preserving the matrix level sends each zero of the signed polynomial with injective complex coordinates to another zero. The constant inclusion carries the two products separately and is injective.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.Admissible`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.Allowable`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.Chart`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.Col`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.Dihedral`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.F`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.K`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.MatEquivalent`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.Normalized`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.PreservesLevel`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.affine`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.affine_constants_admissible`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.constant_matrix_implication`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.diff`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.eval_F`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.eval_matchingPolynomial`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.evenMatching`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.evenProduct`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.evenVertex`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.first`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.last`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.matchingPolynomial`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.minor`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.minor_affine`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.oddMatching`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.oddProduct`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.oddVertex`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.reorder`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.second`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiMatching.third`
