# Arbitrary-input lower bound for the high-terminal chain

## Abstract

Arbitrary full-score placements satisfy the optimized chain supplier's high-terminal lower bound.

**Definition 1.1 (Original label rewards).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.reward`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.reward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural L, native FullScore y, Boolean word b and label r in Fin (L+1), reward uses the original baseline at zero and the original numerical reward at label i+1. Every original label is retained.

**Definition 1.2 (Whole-table weighted score).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.score`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.score` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, FullScore y and output function f on the entire Boolean cube, score sums reward y b (f b) over every word b. The coefficients are arbitrary nonnegative real proof weights, with no probability normalization.

**Definition 1.3 (Complete catalog support).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.support`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, stop flag and FullScore y, support is the finite maximum of score over the original Catalog stop L. The stopped catalog uses increasing schedules; the nonstopped catalog includes reversed and repeated requests. Empty and singleton schedules and all output labels are present.

**Definition 1.4 (Correct class totals).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.gamma`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, FullScore y and address i in Fin L, gamma y i sums C over the original FirstZero b i class. Address i denotes source numerical label i+1.

**Definition 1.5 (Pair class totals).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.pairMass`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.pairMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L, FullScore y and address i, pairMass sums P over the same original first-zero class.

**Definition 1.6 (Early pair support).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.EarlyPair`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.EarlyPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and FullScore y, EarlyPair means P vanishes at every word with a first-zero address at least two. The first two classes are unrestricted, including words whose first two bits are both zero.

**Definition 1.7 (Full pair total).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.pairTotal`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.pairTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and FullScore y, pairTotal is the sum of P over the entire Boolean cube.

**Definition 1.8 (Early correct total).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.early`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.early` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L at least three and FullScore y, early is gamma at zero plus gamma at one, namely the original gamma_1+gamma_2.

**Definition 1.9 (The input-family anchor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.inputAnchor`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.inputAnchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L at least three and FullScore y, inputAnchor equals E+S+t, where E=early, S=pairTotal and t=T. This is the source anchor on the A=0 early-pair family. For other full scores it is only this specified reference value.

**Definition 1.10 (Complete excess at the input anchor).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.delta`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L at least three, stop flag and FullScore y, delta is support stop y minus inputAnchor. For A=0 early-pair inputs it is the original complete excess in the selected catalog.

**Definition 1.11 (Largest late total).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.latePeak`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.latePeak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and FullScore y, latePeak is the maximum of zero and all gamma y i with i.val at least two. No address is relabeled or sorted.

**Definition 1.12 (Two distinct late totals).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.twoLate`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.twoLate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L and FullScore y, twoLate is the maximum sum of gamma over subsets of late addresses of cardinality at most two. The empty set and every singleton are included, so this is the source M2 with zero padding and without an ordering assumption.

**Definition 1.13 (The smaller early capacity).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.earlyCapacity`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.earlyCapacity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L at least three and FullScore y, earlyCapacity is min((E+S)/2, S+min(gamma_1,gamma_2)). It bounds the smaller of the two actual early C+P totals for every nonnegative allocation of P.

**Definition 1.14 (The high-terminal lower bound).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.highLower`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.highLower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L at least three and FullScore y, highLower is max(0, M2-E-S, mu-c0), with mu=latePeak and c0=earlyCapacity. All three quantities use the same original score.

**Theorem 1.15 (Lower bound for every actual input placement).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.arbitrary_input_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.arbitrary_input_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural L at least three and every native FullScore y satisfying EarlyPair, highLower hL y is at most delta hL true y. Thus every source input with A=0, arbitrary C and T, and P supported on the first two first-zero classes satisfies dH <= DeltaO(y). The theorem even permits nonzero A when the reference E+S+t is retained. No equality of reward fibers, fixed support, probability normalization, sorted late profile or high-terminal inequality is a premise.

For any set of at most two distinct first-zero classes, a legal stopped table collects their correct totals together with T. For two ordered addresses i<j, the original table uses outputs i+1, j+1 and zero. The first-zero property places every word of either selected class into its correct stopped cell, and the all-positive word receives zero. All other rewards are nonnegative. Empty and singleton sets use the corresponding shorter tables. This proves the M2 term for arbitrary joint placements.

The stopped head table collects E+S+t, because the two early first-zero classes partition all P. For each late address j, the two legal tables collecting j and one early address give gamma_j-min(Y1,Y2) <= delta, where Ya is the actual early C+P total. Their common P total is S. Nonnegativity gives min(Y1,Y2) <= (E+S)/2 and min(Y1,Y2) <= S+min(gamma_1,gamma_2). Taking the largest late total gives the mu-c0 term. Taking the maximum of the three simultaneous lower bounds proves the statement.

Zero coefficients, ties, unsorted late totals, a single late address at L=3, and arbitrary early-00 P all remain in the quantified domain. The lower bound holds for every T, so in particular it includes t=mu. This result does not construct the chain representative, prove its exact N/O excess, prove quotient or anchor conservation for such a representative, or prove the complementary threshold relocation, certificate and zero-cost quotient equality of Theorem 213.11. Those conclusions require their separate mathematical arguments. This is a consequence of the complete source event geometry, with no literature novelty claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.EarlyPair`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.arbitrary_input_lower_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.delta`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.early`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.earlyCapacity`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.gamma`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.highLower`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.inputAnchor`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.latePeak`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.pairMass`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.pairTotal`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.reward`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.score`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.support`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.twoLate`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction](JointRewardFiberObstruction.md)
