# Alternating Components and Maximal Steiner Switches

## Abstract

Large alternating components identify all successful starts in a point-deleted Steiner system.

**Definition 1.1 (The two pivot matchings).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.pivotMatchings`

*Formalization.* `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.pivotMatchings` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the matching translations for the deleted point and for the fixed remaining pivot.

**Definition 1.2 (A successful starting label).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.SuccessfulStart`

*Formalization.* `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.SuccessfulStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pivot differs from the start and its leave partner. The blocks completing the two pairs with the pivot have third labels that are not leave partners of one another.

**Theorem 1.3 (All successful starting labels).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_successful_starts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_successful_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Delete any point from a finite complete Steiner triple system on r+1 points. The remaining family is a partial Steiner system and has a leave partner map m. For every retained pivot, the embedding of its successful starts into the enlarged point set is exactly the set of vertices in matching components of size at least six. If four divides r, there are at least six such starting labels for every pivot.

The square containing the adjoined point also contains the deleted point, the retained pivot, and its leave partner. All vertices outside the square are eligible retained starts. Pair completion gives the two switch blocks. Their switch is successful exactly where the translations disagree in the two orders. The enlarged carrier has r+2 points, so divisibility of r by four forces a large component.

**Theorem 1.4 (The first deficit without a switch hypothesis).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_first_deficit_of_four_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_first_deficit_of_four_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive row dimension d and nonzero residue modulus 3r. Suppose the lifted cross-row family has pair completion, distinct rows, and pair uniqueness. If a complete Steiner system exists on r+1 points and four divides r, the largest internal extension has size N equal to 3^d r^2 plus 3^(d+1) times floor(r(r−2)/6). There are saturated internal extensions of sizes N and N−1, and every internal extension has size at most N.

Choose a successful start at any retained pivot and apply the one-class switch construction. The matching packing supplies the upper bound in every class.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.SuccessfulStart`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.pivotMatchings`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_first_deficit_of_four_dvd`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches.point_deleted_successful_starts`
- Dependency: [D5/S3/Combinatorics/Matroids/AlternatingMatchingComponents](AlternatingMatchingComponents.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerMatchingTranslations](SteinerMatchingTranslations.md)
