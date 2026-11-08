# The balanced high-terminal chain

## Abstract

The native balanced chain preserves coefficient data and has equal exact complete N and O costs at high terminal mass.

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

Zero coefficients, ties, unsorted late totals, a single late address at L=3, and arbitrary early-00 P all remain in the quantified domain. The lower bound holds for every T, so in particular it includes t=mu. The balanced construction below uses this lower bound to identify its exact support. The complementary threshold relocation, certificate and zero-cost quotient equality of Theorem 213.11 require separate arguments. This is a consequence of the complete source event geometry, with no literature novelty claim.

**Definition 1.16 (Balanced early allocation).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balancedSplit`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balancedSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For nonnegative early correct totals a,b and pair mass S, the first allocation is min(S,max(0,(b+S-a)/2)). The second allocation is S minus the first. Their two correct-plus-pair totals have minimum min((a+b+S)/2,S+min(a,b)).

**Definition 1.17 (Native chain score).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balancedChain`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balancedChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every L at least three, arbitrary nonnegative g indexed by Fin L and nonnegative S,t, balancedChain is a native FullScore on the entire Boolean cube. It places C=g(i) at the word with i initial ones followed by zeros. The first two such words carry the balanced pair masses. A vanishes everywhere, T=t, and every other C and P row is zero. The first chain word has early bits 00, so its P mass is part of the original early-00 class.

**Theorem 1.18 (Exact complete high-terminal costs).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balanced_chain_exact`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balanced_chain_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L at least three, nonnegative profile g and masses S,t, let V be the native balancedChain. Assume latePeak(V) is at most t. Then beta(V)=g, coefficientMass(V)=sum(g)+S+t, pairTotal(V)=S, and inputAnchor(V)=g(0)+g(1)+S+t. The score satisfies EarlyPair and every gamma(V,i)=g(i). Both complete excesses equal max(highLower(V),latePeak(V)-early(V)). Thus the source value is max(dH,mu-E), with c0 and M2 defined from the same unsorted profile.

Every complete native table, including a short, repeated or reversed nonstopped schedule, depends on at most two distinct addresses. On the chain its restrictions coincide with an increasing stopped pair table. The chain has no 01 cell. If the first query is the first address, its initial cell has reward at most the first early C+P total, and the middle cell earns either the second early C+P total or one late correct total. Otherwise both early words lie in the initial cell; its early or zero label earns at most one of the two early totals or S. If its label is late, the initial and middle cells collect at most two distinct late totals. The final cell earns at most t, since all its numerical labels are late. These bounds account for all labels, including zero, and give the complete upper bound.

The arbitrary-input theorem supplies dH as a lower bound for this actual chain. For each late address j, the native stopped pair querying the second early address and j, with labels zero,j+1,zero, collects S+g(j)+t. Maximizing over late j supplies mu-E. The two lower bounds match the complete upper bound. The clamped split identifies the smaller early total with c0. No chosen label, desired score value or support equation is an assumption of the construction.

The result retains arbitrary L, unsorted profiles, ties, zero masses, t=mu and the actual single late address at L=3. It does not assert max(dH,mu-E) is below every arbitrary input's O excess: that comparison additionally needs mu at most E+DeltaO(input).

**Theorem 1.19 (Comparison on the source branch).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balanced_chain_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balanced_chain_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every L at least three and every native FullScore y, assume A vanishes, P is supported on the first two first-zero classes, latePeak(y) is at most T, and latePeak(y) is at most early(y)+delta(true,y). Then an actual balanced native chain V has vanishing A, EarlyPair, the same beta, coefficientMass and inputAnchor, and delta(false,V) is at most delta(true,y). The final branch condition is essential to this comparison; it is not inferred from the high-terminal hypothesis.

Use gamma(y), pairTotal(y) and T as the construction parameters. Apply the original numerical_total partition identity to the same FullScore with P set to zero, then commute the finite sums. The resulting first-zero totals sum to the original C mass. This identifies the entire coefficient mass as well as beta and the anchor. The exact chain theorem reduces its complete N excess to the maximum of dH and mu-E. The retained arbitrary-input theorem bounds the first term and the stated branch condition bounds the second. No additional restriction on the joint input placement, early-00 P, ties, zero coefficients or the single late address is imposed.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.EarlyPair`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.arbitrary_input_lower_bound`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balancedChain`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balancedSplit`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balanced_chain_comparison`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/HighTerminalChain.balanced_chain_exact`
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
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PreselectedResidualBound](PreselectedResidualBound.md)
