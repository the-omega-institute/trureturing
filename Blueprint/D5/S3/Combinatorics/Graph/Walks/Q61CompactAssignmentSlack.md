# Compact positive assignment slack

## Abstract

Compact positive assignment slack and finite-block losses for min-plus walks.

In the complete-Bob model of Meyerovitch–Young Question 6.1, each Alice edge has a real cost matrix on a finite nonempty set of m Bob states. Rows are sources and columns are destinations. For a fixed legal Alice walk, Bob minimizes the sum of the paired costs with both endpoints free. Zero initial scores give every starting state the same initial cost, and the least terminal score is the payoff. https://arxiv.org/html/2603.21449v1#S4.E6

Fix a per-state rate r and an Alice vertex potential H in total-score units. The chosen permutation on an edge has assignment cost at most m times r plus the source potential minus the target potential. When this bound is supplied for the cheapest assignment in per-state units, choose a minimizing permutation on each edge and multiply the bound and potential by m.

**Theorem 1.1 (Compactness of the anchored score box).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.isCompact_projectiveBox`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.isCompact_projectiveBox` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the score at an anchor o gives a representative with coordinate o equal to zero. The projective box consists of these anchored vectors with every ordered coordinate difference at most B. It is a closed subset of the product of the intervals from −B to B and includes its boundary.

**Theorem 1.2 (The box contains the normalized scores after every prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.normalize_endpointScores_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.normalize_endpointScores_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose all ordered differences between entries in the same row of each edge matrix are at most B. To bound the difference of two output scores, use a source attaining the minimum for the second destination as a candidate for the first. Its input score cancels, leaving the within-row bound. An input whose normalization is in the box therefore stays in the box after normalization at every prefix.

**Theorem 1.3 (Slack vanishes exactly on tight walks).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.assignmentSlack_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.assignmentSlack_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a legal n-edge walk from s to t, the assignment slack is n times m times r plus H(s) minus H(t), minus the gain in the sum of Bob's scores. The assignment certificate makes this slack nonnegative. It is zero exactly when every chosen assignment saturates the edge cap and all its column guards hold at the actual prefix scores from the given input. The guards allow ties.

**Theorem 1.4 (Exact addition of block losses).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.assignmentSlack_append`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.assignmentSlack_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a split at an intermediate vertex, the slack of the concatenated word equals the first block's slack plus the second block's slack evaluated at the actual scores after the first block. The intervening potential and sum of scores cancel. A common translation of the input translates every later score by the same constant, so the slack can also be evaluated at the normalized input to each block.

**Theorem 1.5 (An attained positive minimum for blocks of fixed length).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.compact_block_assignment_slack`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.compact_block_assignment_slack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a finite Alice graph and fix a block length N. For each legal word of length N with specified endpoints, slack is continuous in the input because each update takes a finite minimum of affine functions. There are finitely many word and endpoint choices, so their slack images of the projective box form a compact union.

If every legal N-edge walk fails tightness from every input in the box, every slack in the union is strictly positive. When the union is nonempty, its least element δ is positive and realized by some legal block and input. An empty union permits any positive lower bound.

**Theorem 1.6 (A finite-horizon payoff deficit for every complete block).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.compact_block_payoff_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.compact_block_payoff_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume N is positive, B is nonnegative, and the same-row bounds hold on every edge. If no legal N-edge walk is tight from any input in the box, take δ from the compact block minimum. Zero initial scores are in the box. Every complete block contributes at least δ at its own prefix scores and the remaining suffix contributes nonnegative slack.

For any legal n-edge walk from s to t, m times its zero-start, free-terminal payoff plus ⌊n/N⌋δ is at most n times m times r plus H(s) minus H(t). The least terminal score is at most the average terminal score, which converts the total-score bound to the payoff bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.assignmentSlack_append`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.assignmentSlack_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.compact_block_assignment_slack`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.compact_block_payoff_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.isCompact_projectiveBox`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61CompactAssignmentSlack.normalize_endpointScores_mem`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards](MeyerovitchYoungQ61AssignmentGuards.md)
