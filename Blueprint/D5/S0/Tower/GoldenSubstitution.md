# Golden Substitution

## Abstract

Level refinement inserts one name per large gap at the inverse golden fraction.

Refining the golden tower by one level embeds the old names into the new enumeration and inserts fresh names. The insertion pattern is the tower's own substitution dynamics acting on gap types.

**Definition 1.1 (Level embedding of old names).**

Lean statement: `D5/S0/Tower/GoldenSubstitution.levelEmbedding`

*Formalization.* `D5/S0/Tower/GoldenSubstitution.levelEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every level-Q name reappears at level Q plus one with the same value, strictly monotonically, reusing the frozen enumeration vocabulary.

**Definition 1.2 (Inserted name indices).**

Lean statement: `D5/S0/Tower/GoldenSubstitution.insertedNameIndices`

*Formalization.* `D5/S0/Tower/GoldenSubstitution.insertedNameIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complement of the embedded image: the fresh level-(Q+1) names that refine the old gaps.

**Theorem 1.3 (Each large gap gains exactly one name).**

$$\forall Q \in N,\; \operatorname{insertedCount}\left(Q, i\right) = \operatorname{largeGapIndicator}\left(Q, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/GoldenSubstitution.golden_gap_insertion_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From level two onward a refinement step inserts exactly one new name into each large gap and none into any small gap; the unique insertion point splits the large gap into a new large then a new small gap at the inverse-golden fraction from the left. Gap types therefore evolve by the golden substitution: small becomes large, large becomes large then small.

## References

- Truth anchor: `D5/S0/Tower/GoldenSubstitution.golden_gap_insertion_count`
- Truth anchor: `D5/S0/Tower/GoldenSubstitution.insertedNameIndices`
- Truth anchor: `D5/S0/Tower/GoldenSubstitution.levelEmbedding`
- Dependency: [D5/S0/Tower/GoldenGaps](GoldenGaps.md)
