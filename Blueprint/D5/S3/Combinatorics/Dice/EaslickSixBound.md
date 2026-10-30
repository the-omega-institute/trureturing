# EaslickSixBound

## Abstract

The complete dice conjecture follows from an exhaustive six-face upper bound and uniform longer cycles.

**Theorem 1.1 (The global six-face upper bound).**

$$\forall k \in \mathit{Nat},\; \operatorname{HasCycle}\left(6, k\right) \Rightarrow k \le 6$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.six_cycle_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural k, HasCycle(6,k) implies k at most six. A complete recursive enumeration includes all 462 sorted six-face dice with labels from one through six, including repetitions and the standard die. Every score-19 edge weakly decreases the certified rank. A closed cycle therefore has one rank and lies in its entire rank fiber. All fibers have at most seven elements. In each seven-element fiber, two distinct vertices have the same unique internal successor. A seven-cycle would exhaust that fiber, contradicting injectivity of the cyclic successor operation on distinct vertices. The certificate is checked by Lean kernel reduction; its rank data are a witness, never an assumed law.

**Theorem 1.2 (The attained six-face maximum).**

$$\operatorname{S}\left(6\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.S_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

S(6) holds: an explicit six-cycle attains the global upper bound of six. The upper bound applies to every simple directed cycle in the full graph at the true least attainable strict-win probability above one half.

**Theorem 1.3 (The complete Easlick conjecture).**

$$\operatorname{S}\left(6\right) \land \left(\forall n \in \mathit{Nat},\; 7 \le n \Rightarrow \left(\neg \operatorname{S}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

The complete proposition is S(6) and, for every natural n at least seven, not S(n). Natural n faithfully represents the source integer range n at least three. Dice are all nondecreasing lists of n labels in the interval from one through n. Repeated faces and the standard tuple remain included. Strict-win probability is unconditional on the uniform independent product of face indices. The attained minimum is proved, not taken from the author parity formula. S quantifies over all longer simple cycles, with no finite cutoff.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.S_six`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.six_cycle_bound`
- Dependency: [D5/S3/Combinatorics/Dice/EaslickPaddedCycles](EaslickPaddedCycles.md)
