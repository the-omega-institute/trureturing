# Local Classification of Labelled Choices

## Abstract

Interior balance is local: future classes cannot alter retired vertices, and the six live residues distinguish the admissible labelled transitions.

**Theorem 1.1 (Future edges miss both retired residues).**

Lean statement: `D5/S3/Combinatorics/Zigzag/ChoiceClassification.edgeFlow_future_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/ChoiceClassification.edgeFlow_future_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under 3<=j<k<=n-j, an edge of class k has zero contribution at j-1 and its negative. The proof checks every one of the six source endpoint formulas using integer representatives and the ZMod distinctness criterion. This is the reason a later choice cannot repair a failed old balance equation.

**Theorem 1.2 (The strict interior frontier is distinct).**

Lean statement: `D5/S3/Combinatorics/Zigzag/ChoiceClassification.frontierVertex_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/ChoiceClassification.frontierVertex_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When 3<=j and 2j<n, the residues 1, -1, j-1, 1-j, j, -j are pairwise distinct. This permits the local flow equations to be read independently. The strict inequality deliberately excludes the parity boundary, which Retirement handles separately.

**Theorem 1.3 (Local balance forces a listed transition).**

Lean statement: `D5/S3/Combinatorics/Zigzag/ChoiceClassification.transition_labels_of_local_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/ChoiceClassification.transition_labels_of_local_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual charge at each just-retired residue determines the allowed low and high form pair for the next state. The proof uses the complete finite form table in both signs; this converse classification is needed to decode arbitrary balanced choices, not only to verify paths already built.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/ChoiceClassification.edgeFlow_future_zero`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/ChoiceClassification.frontierVertex_injective`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/ChoiceClassification.transition_labels_of_local_balance`
- Dependency: [D5/S3/Combinatorics/Zigzag/Retirement](Retirement.md)
