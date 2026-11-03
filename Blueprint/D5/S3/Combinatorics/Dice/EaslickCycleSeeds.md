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

**Definition 1.2 (Executable successive-edge scan).**

$$\forall A \in \mathit{Type}, edge \in (A \to (A \to \mathit{Bool})), c \in \operatorname{List}\left(A\right),\; \operatorname{checkSteps}\left(\mathit{edge}, c\right) = \mathit{true} \Leftrightarrow \left(\forall i \in \mathit{Nat},\; i + 1 < \operatorname{length}\left(c\right) \Rightarrow \mathit{edge}\left(\operatorname{at}\left(c, i\right), \operatorname{at}\left(c, i + 1\right)\right) = \mathit{true}\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkSteps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For arbitrary encoded vertices and a Boolean edge function, recursively scan each adjacent pair. Empty and singleton lists have no edge obligation. This executable operation takes no semantic chain law.

**Definition 1.3 (Executable die validation).**

$$\forall n \in \mathit{Nat}, d \in \operatorname{List}\left(\mathit{Nat}\right),\; \operatorname{checkDie}\left(n, d\right) = \mathit{true} \Leftrightarrow \left(\left(\operatorname{length}\left(d\right) = n \land \left(\forall i \in \mathit{Nat},\; i + 1 < \operatorname{length}\left(d\right) \Rightarrow \operatorname{at}\left(d, i\right) \le \operatorname{at}\left(d, i + 1\right)\right)\right) \land \left(\forall x \in \mathit{Nat},\; x \in d \Rightarrow \left(1 \le x \land x \le n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkDie` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

At arbitrary face count n, check the exact list length, successive nondecreasing labels and the lower and upper label bounds. Repeated labels are allowed. Soundness derives global pairwise order using transitivity.

**Definition 1.4 (Executable arbitrary cycle validation).**

$$\forall n \in \mathit{Nat}, c \in \operatorname{List}\left(\operatorname{List}\left(\mathit{Nat}\right)\right),\; \operatorname{checkCycle}\left(n, c\right) = \mathit{true} \Leftrightarrow \left(\left(\left(c \ne \operatorname{nil}\left(\right) \land \operatorname{length}\left(\operatorname{dedup}\left(c\right)\right) = \operatorname{length}\left(c\right)\right) \land \left(\forall d \in \operatorname{List}\left(\mathit{Nat}\right),\; d \in c \Rightarrow \operatorname{checkDie}\left(n, d\right) = \mathit{true}\right)\right) \land \left(\forall i \in \mathit{Nat},\; i < \operatorname{length}\left(c\right) \Rightarrow \operatorname{winCount}\left(\operatorname{at}\left(c, i\right), \operatorname{at}\left(c, \left(i + 1\right) \bmod \operatorname{length}\left(c\right)\right)\right) = \operatorname{threshold}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkCycle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For arbitrary n and any finite list of encoded dice, check nonemptiness, duplicate removal preserving length, die validation and exact win counts on the closed list. This scans the actual input and never assumes validity, distinctness or a graph law.

**Theorem 1.5 (General cycle checker soundness).**

$$\forall n \in \mathit{Nat}, c \in \operatorname{List}\left(\operatorname{List}\left(\mathit{Nat}\right)\right),\; \left(3 \le n \land \operatorname{checkCycle}\left(n, c\right) = \mathit{true}\right) \Rightarrow \operatorname{HasCycle}\left(n, \operatorname{length}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkCycle_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every n at least three and every encoded finite input c, successful checkCycle reconstructs HasCycle(n,length(c)) in the original graph defined by actual minimum unconditional win probabilities. Its only checking premise is the executable Boolean result; the true-minimum bridge supplies the interpretation of the tested edge counts.

**Theorem 1.6 (Actual first checker inputs).**

$$\forall n \in \mathit{Nat},\; \left(n = 6 \lor \left(n = 7 \lor \left(n = 8 \lor \left(n = 9 \lor \left(n = 10 \lor n = 11\right)\right)\right)\right)\right) \Rightarrow \operatorname{checkCycle}\left(n, \operatorname{sourceSeed}\left(n\right)\right) = \mathit{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.sourceSeed_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

The unchanged six source and derived seed lists, at n in 6,7,8,9,10,11, pass checkCycle by kernel reduction. This is a computed first-instance certificate for the general checker. It is consumed by checkCycle_sound in finite_cycle_witnesses and then by the complete conjecture proof; it is not an independent finite-case resolution.

**Theorem 1.7 (The verified finite cycle lengths).**

$$\left(\left(\left(\left(\operatorname{HasCycle}\left(6, 6\right) \land \operatorname{HasCycle}\left(7, 14\right)\right) \land \operatorname{HasCycle}\left(8, 29\right)\right) \land \operatorname{HasCycle}\left(9, 10\right)\right) \land \operatorname{HasCycle}\left(10, 110\right)\right) \land \operatorname{HasCycle}\left(11, 14\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.finite_cycle_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

There is a simple minimum-advantage cycle of length six for six-face dice, length fourteen for seven-face dice, length twenty-nine for eight-face dice, length ten for nine-face dice, length one hundred ten for ten-face dice, and length fourteen for eleven-face dice. Every die is sorted with valid labels, all vertices in each cycle are distinct, and every edge including the closing edge has the true minimum probability above one half. These assertions supply finite seeds and do not assert the unbounded parameter statement or the global upper bound at six.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkCycle`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkCycle_sound`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkDie`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.checkSteps`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.finite_cycle_witnesses`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.sourceSeed`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickCycleSeeds.sourceSeed_check`
- Dependency: [D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage](EaslickMinimalAdvantage.md)
