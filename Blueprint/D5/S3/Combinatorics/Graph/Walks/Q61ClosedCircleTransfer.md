# Closed two-circle register transfers

## Abstract

Exact closed-circle transfers via tight three-state min-plus matrix words.

The ordinary proof of undecidable exact attainment at value zero in theory PR 54 uses these transfers as local steps in the full machine graph. The marked-return payoff argument in q61-return-reward-response.txt uses the completed transfers after the literal reset to P. Lean coverage here is the local passage. https://github.com/the-omega-institute/trureturing-source-theories/pull/54

**Theorem 1.1 (The two-loop passage forces the input and output).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.run_word_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.run_word_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Encode integers on the unit circle using the injective orbit of √2 − 1. For arbitrary circle inputs, the row with loop counts k and j completes exactly when the input encodes (bk + r, 0), j = ak, and the output encodes (ak + s, 0).

**Theorem 1.2 (Finite branches realize every closed lift of a permitted step).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.exists_branch`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.exists_branch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any closed source and target lifts of a permitted circle step, a branch uses bounded integer wraps and selects the source lift 0 or 1 independently at each tested coordinate. Its closed rectangular guard contains the source and its translation reaches the chosen target.

**Theorem 1.3 (Tight matrix words implement the exact residue transfer).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.compiled_passage_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.compiled_passage_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each branch matrix has nonpositive total score gain, with equality exactly on its guard. From any real three-state score in the translated square, a compiled passage has zero total gain and the stated projected endpoint exactly when the input encodes (n, 0) for positive n with (n − 1) mod b = r − 1, and the endpoint encodes (a⌊(n − 1)/b⌋ + s, 0). Here 1 ≤ r ≤ b.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.compiled_passage_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.exists_branch`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer.run_word_iff`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61AssignmentGuards](MeyerovitchYoungQ61AssignmentGuards.md)
