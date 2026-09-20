# Ordered Zeckendorf Paths and the Inversion Potential

## Abstract

Every finite legal ordered path is bounded by its carry reward and initial inversions.

A state is one list of natural-number raw W indices. Decode maps each index through successor to the positive paper indices; n zeros thus represent n ones. Multiplicities are obtained through Multiset.toFinsupp. Move records the position of its adjacent window and one of five actions: an inversion switch, combining ones, splitting twos, a general split, or a consecutive merge. No predecessor map is used.

**Theorem 1.1 (The path potential bound).**

$$Path\left(s, t, length, weight\right) \Rightarrow length + inv\left(decode\left(t\right)\right) \le inv\left(decode\left(s\right)\right) + weight$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/OrderedGame.path_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite legal path, actual move count plus final inversions is at most initial inversions plus summed carry reward. Switch reward is zero. In positive indices the other rewards are c1-1, c2-1, c(i-1)+ci-1 for a split at i greater than two, and c(a+1) for a merge at a. Thus rewards include the carry itself. The proof telescopes the existing four local inversion bounds; a switch removes exactly one inversion. There is no terminality or strategy assumption.

LGSPath keeps every permitted inversion-switch choice. Its priority restarts after every move: switches, leftmost ones, rightmost split, then leftmost consecutive merge. Conjecture17 records nonvacuous complete LGS existence for every positive n and the comparison of every complete LGS run with every legal terminal competitor. That proposition is defined but not proved. The path bound alone does not establish attainment or weighted greedy optimality.

## References

- Truth anchor: `D5/S1/Digit/Carry/OrderedGame.path_potential`
- Dependency: [D5/S1/Digit/Carry/ListInversions](ListInversions.md)
- Dependency: [D5/S1/Digit/Raw](../Raw.md)
