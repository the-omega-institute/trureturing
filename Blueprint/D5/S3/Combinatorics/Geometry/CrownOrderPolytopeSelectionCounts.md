# Counting selected odd blocks

## Abstract

Profile counts and the one-block edge give the full selection count.

These counts implement source Lemma 3.4 together with the marked count in Lemma 3.5. All support conditions and the one-block contribution are explicit.

**Theorem 1.1 (Count for a fixed odd-block profile).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_profile_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_profile_card` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two, i at least two and m positive, the selections with i boundary cuts and 2m odd blocks that yield d+2 augmented blocks have the exact marked cardinality stated in Lean. The binomial factor choosing i-d selected odd blocks is zero when d exceeds i; that support condition is explicit.

**Theorem 1.2 (The unique one-block contribution).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_oneBlock_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_oneBlock_card` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every positive n, selections whose underlying cycle partition has one block contribute exactly one when d equals one and zero otherwise. The single even block permits only the empty odd-block selection.

**Theorem 1.3 (Sum of all selection profiles).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_card` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two, the cardinality of all selections producing d+2 augmented blocks equals the one-block correction plus the finite sum of the exact profile counts. Division by the number of markings is justified within the count.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_oneBlock_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeSelectionCounts.crownOddBlockSelection_profile_card`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery](CrownOrderPolytopeEndpointRecovery.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeMarkedCuts](CrownOrderPolytopeMarkedCuts.md)
