# Assignment guards for Meyerovitch–Young Question 6.1

## Abstract

Exact assignment guards and potential bounds for finite min-plus walks.

In the offline game, Alice first chooses the whole legal edge word. Bob minimizes its paired cost over walks of that length with both endpoints free. Here Bob has a finite nonempty state set and one directed edge per ordered pair, including loops. The rows of each cost matrix index Bob's sources and the columns index his destinations. The certificates use sums of endpoint scores. The offline payoff is the least endpoint score from zero initial scores. https://arxiv.org/html/2603.21449v1#S4.E6

**Theorem 1.1 (Attained minima at individual endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.endpointScores_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.endpointScores_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting with all scores zero, after any word the score at each destination is the minimum cost of the complete Bob walks ending there and having the length of the word. An attaining walk exists with some starting vertex. For each possible source of the final edge, add that edge's matrix entry to the preceding endpoint minimum, then take the least of those candidates.

**Theorem 1.2 (The free-endpoint payoff of a fixed word).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.matrixMinimum_eq_inf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.matrixMinimum_eq_inf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix minimum from the complete matrix reduction is the least coordinate of the final score vector from zero. Taking the minimum over destinations frees the final endpoint, and initializing every score at zero frees the initial endpoint. The empty word has cost zero.

**Theorem 1.3 (Exact equality at a chosen assignment bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.assignment_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.assignment_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a linearly ordered commutative ring, fix any input vector and any permutation assigning a source to each destination. The change in the sum of endpoint scores is at most the sum of matrix entries selected by the permutation.

The sum of the input coordinates cancels because each source is assigned once. Equality holds exactly when every chosen candidate attains its column minimum. For each column and competing source, the input score of its assigned source minus the competing source's input score must be at most the competitor's matrix entry minus the assigned entry. These weak inequalities include ties.

**Theorem 1.4 (The affine permutation on score differences).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.endpointUpdate_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.endpointUpdate_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When all the assignment guards hold, the output difference between a destination and any reference destination equals the input difference between their assigned sources plus the difference between their assigned entries.

**Theorem 1.5 (Telescoping and equality along a legal walk).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.walk_assignment_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.walk_assignment_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assign a matrix, a permutation and a cap to each Alice edge, and supply a potential on Alice's vertices. Assume the assigned cost on each edge is at most its cap plus the source potential minus the target potential. From any initial score vector, the total change in the sum of endpoint scores along a legal walk is bounded by the sum of the traversed caps plus the initial vertex potential minus the terminal vertex potential.

Each step has two nonnegative slacks, one for the assignment inequality and one for the potential-adjusted cap. The intermediate potentials cancel. Equality holds exactly when each step attains its potential-adjusted cap in assignment cost and its guards hold at the input produced by the actual min-plus recurrence on the preceding prefix. The empty walk satisfies the equality condition.

**Theorem 1.6 (A complete matrix for prescribed pairwise guards).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.guardMatrix_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.guardMatrix_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a linearly ordered field, center the prescribed offsets by subtracting their mean and place the centered offsets in the assigned entries. In each column, add the corresponding pairwise guard bound to the centered offset to obtain the entry at each competing source.

The chosen assignment has cost zero. For every input the total score increment is nonpositive, and it is zero exactly when all prescribed ordered-pair difference bounds hold. On that guard the output difference between any two destinations is the difference between their permuted input coordinates plus the difference of their original offsets.

**Theorem 1.7 (Realization of a finite system of closed guards).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.exists_matrix_realizing_bounded_guards`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.exists_matrix_realizing_bounded_guards` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite family of closed difference inequalities between distinct coordinates and assume that satisfying them bounds every ordered difference between distinct coordinates above by a common constant. For any prescribed permutation and offsets over a linearly ordered field, a complete matrix has chosen assignment cost zero and nonpositive total score increment for every input. The increment is zero exactly on that guard, where the matrix implements the prescribed affine permutation on differences.

For each ordered pair with multiple bounds, use the least bound. For a missing pair, use the common upper bound already implied by the guard system. The resulting pairwise system defines exactly the same inputs.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.assignment_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.endpointScores_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.endpointUpdate_difference`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.exists_matrix_realizing_bounded_guards`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.guardMatrix_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.matrixMinimum_eq_inf`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards.walk_assignment_certificate`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete](MeyerovitchYoungQ61Complete.md)
