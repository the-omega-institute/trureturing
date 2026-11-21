# The DFA intersection encoding for Meyerovitch–Young Question 6.1

## Abstract

The finite-horizon DFA intersection encoding counts charged completed segments.

Take a finite nonempty state space with deterministic transitions for every ordinary letter, a nonempty reset set, and a set of accepting states. For a family of complete automata, these are the disjoint union of their states, the initial states of its components, and the accepting states of its components, respectively. Alice has one vertex with an edge for each ordinary letter and a delimiter edge. Bob has one edge per ordered pair of states. The free-endpoint objective is the sum of integer costs along the paired walks. https://arxiv.org/html/2603.21449v1#S4.E6

An ordinary edge costs zero if it follows the deterministic transition and two otherwise. A delimiter edge ending in the reset set costs one if its departure state accepts and zero otherwise. A delimiter edge ending outside the reset set costs two.

**Theorem 1.1 (Exact cost and minimizing endpoints).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection.matrixMinimum_eq_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection.matrixMinimum_eq_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every word, the free-endpoint matrix minimum equals the number of charged completed segments. Its minimizing endpoints are exactly the states in the scan's current set.

Start the scan at zero with the entire state space. An ordinary letter sends the current set through the deterministic transition and preserves the count. A delimiter adds one when all states in the current set accept, and then replaces the set by the reset set. The final unfinished segment contributes zero.

At each prefix the actual endpoint score is obtained by minimizing over the departure state of the last edge. An ordinary letter preserves the minimum, and the only ways to attain it follow a cost-zero transition from a previous minimizer. At a delimiter the common score inside the reset set increases by one exactly when every previous minimizer accepts, because nonminimizers have integer scores at least one higher. Outside the reset set each score is two above the previous minimum.

**Theorem 1.2 (Detection of a charged segment).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection.matrixMinimum_pos_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection.matrixMinimum_pos_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The free-endpoint matrix minimum of a word is positive exactly when it has a delimiter whose preceding prefix leaves the scan's current state set contained in the accepting set. This recognizes a completed segment whose ordinary run accepts from every state in its starting set.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection.matrixMinimum_eq_score`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61DFAIntersection.matrixMinimum_pos_iff`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete](MeyerovitchYoungQ61Complete.md)
