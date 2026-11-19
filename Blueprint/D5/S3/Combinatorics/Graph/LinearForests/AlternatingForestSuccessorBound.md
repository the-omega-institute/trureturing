# Successors of a component in an oriented alternating forest

## Abstract

Remaining heads control a connector in an alternating cycle completion.

**Theorem 1.1 (Probability bound for a set of successor components).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingForestSuccessorBound.mass_of_successor_components`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/AlternatingForestSuccessorBound.mass_of_successor_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prescribe directed edges on a finite set with n vertices of each color. Let m be the number of prescribed edges and assume m plus two is at most n. Sample a uniform directed alternating single cycle that extends all prescribed edges. The sampled cycle forces the prescribed edges to alternate and to have at most one incoming and outgoing edge per vertex. Any directed loop among them would traverse the whole cycle, contradicting the strict edge bound. Each path component has a head and a tail. Given a component and a set of other components, the probability that the successor of its tail is a head in that set is at most the size of the set divided by n minus m minus one. Each prescribed edge can remove at most one head of either color, so the remaining count supplies the denominator.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/AlternatingForestSuccessorBound.mass_of_successor_components`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/AlternatingSuccessorSetBound](AlternatingSuccessorSetBound.md)
