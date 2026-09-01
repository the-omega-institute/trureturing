# Omnicomplete Indifferent States

## Abstract

An omnicomplete indifferent state has full support, symmetry invariance, prescribed finite projections, and zero completion defect.

**Definition 1.1 (Four conditions for an omnicomplete indifferent state).**

Lean statement: `D5/S3/Observer/Completion/OmnicompleteIndifferentState.OmnicompleteSystem`

*Formalization.* `D5/S3/Observer/Completion/OmnicompleteIndifferentState.OmnicompleteSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structure carries a measure whose support is the whole state space, whose pushforward by every symmetry is itself, whose pushforward along every finite projection is the prescribed finite measure, and whose completion defect vanishes at every finite level.

The conditions are jointly realizable. On the two-point Boolean state space, counting measure has full support and gives each singleton mass one; the one-element group acts trivially, every finite projection is the identity, and every defect is zero. The Lean theorem exists_bool_omnicomplete_indifferent_state constructs this nontrivial instance.

## References

- Truth anchor: `D5/S3/Observer/Completion/OmnicompleteIndifferentState.OmnicompleteSystem`
