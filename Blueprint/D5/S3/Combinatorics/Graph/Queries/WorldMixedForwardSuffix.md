# Fresh binary suffixes under a graph prior

## Abstract

A conditional bound for a suffix selected as a function of the graph world.

**Definition 1.1 (Weight of a fresh binary suffix).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.suffixWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.suffixWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each newly observed position contributes a factor of one half.

**Theorem 1.2 (Conditioning and mixing fresh suffix bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.joint_fresh_suffix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.joint_fresh_suffix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Draw a world from the prior. At each position in a finite set, the world specifies two distinct choices. Independently of the world and of the other positions, choose a uniform order at each position. Fix a prefix observation. For each world, choose a suffix observation at positions disjoint from the prefix positions.

Fix an event of worlds. In every world belonging to that event, suppose the suffix observes at least the stated number of distinct positions. When the prefix has positive mass, the conditional probability of that event and the suffix together is at most the posterior probability of the world event times the corresponding fresh suffix weight. The formal inequality uses extended nonnegative real ratios.

In each world, a compatible prefix and suffix satisfy the fixed-world likelihood bound. Incompatible observations contribute zero to the joint event. Sum the worldwise inequalities, weighted by the prior, before dividing by the mass of the prefix.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.joint_fresh_suffix_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.suffixWeight`
- Dependency: [D5/S3/Combinatorics/Graph/Queries/ForwardSuffixLaw](ForwardSuffixLaw.md)
