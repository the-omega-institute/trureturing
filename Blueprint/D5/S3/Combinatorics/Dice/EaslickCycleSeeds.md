# Finite cycle seeds

## Abstract

Explicit simple cycles provide small seeds for uniform nested padding.

**Definition 1.1 (The six seed lists).**

Lean statement: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.sourceSeed`

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.sourceSeed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

The function sourceSeed assigns the explicit sorted-die cycles at six, seven, eight, nine, ten and eleven faces; it is empty at all other natural arguments. The corresponding lengths are 6,14,29,10,110,14. The lists omit the repeated closure row. The seven- through ten-face lists are the source lists in Appendices G through J, and the eleven-face list is obtained from the seven-face list by shifting each seed label by two and adding two low and two high faces in alternating nested intervals.

**Theorem 1.2 (The verified finite cycle lengths).**

$$\left(\left(\left(\left(\operatorname{HasCycle}\left(6, 6\right) \land \operatorname{HasCycle}\left(7, 14\right)\right) \land \operatorname{HasCycle}\left(8, 29\right)\right) \land \operatorname{HasCycle}\left(9, 10\right)\right) \land \operatorname{HasCycle}\left(10, 110\right)\right) \land \operatorname{HasCycle}\left(11, 14\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.finite_cycle_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

There is a simple minimum-advantage cycle of length six for six-face dice, length fourteen for seven-face dice, length twenty-nine for eight-face dice, length ten for nine-face dice, length one hundred ten for ten-face dice, and length fourteen for eleven-face dice. Every die is sorted with valid labels, all vertices in each cycle are distinct, and every edge including the closing edge has the true minimum probability above one half. These assertions supply finite seeds and do not assert the unbounded parameter statement or the global upper bound at six.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.finite_cycle_witnesses`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.sourceSeed`
- Dependency: [D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage](EaslickMinimalAdvantage.md)
