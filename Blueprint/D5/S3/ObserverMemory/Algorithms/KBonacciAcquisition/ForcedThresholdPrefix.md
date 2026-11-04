# Forced thresholds and actual common branches

## Abstract

Actual adaptive selectors preserve one coherent first-tour zero archive for arbitrary blind bands.

**Definition 1.1 (Immutable threshold and blind band).**

$$\forall Y \in Type,\; \forall k \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall labels \in \operatorname{ZMod}\left(k + 1\right) \to Y,\; \forall outside \in Y,\; \forall rejected \in Y,\; \forall bottom \in Y,\; \operatorname{initialLabel}\left(k, a, labels, outside, rejected, bottom, none\right) = bottom \land \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall phase \in \operatorname{ZMod}\left(k + 1\right),\; \forall s \in \mathbb{N},\; \operatorname{initialLabel}\left(k, a, labels, outside, rejected, bottom, \operatorname{some}\left(\langle v,phase,s\rangle\right)\right) = \operatorname{ifThenElse}\left(k - a \le s, rejected, \operatorname{ifThenElse}\left(0 < \operatorname{val}\left(-phase\right) \land \operatorname{val}\left(-phase\right) < a, labels\left(-phase\right), outside\right)\right)\right)$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.initialLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtraction is natural subtraction. On a live INITIAL record, the tail test has priority: tails at least k-a receive rejected. Smaller tails receive labels(-phase) when 0<(-phase).val<a and outside otherwise. The separately known INITIAL rejection receives bottom. The total phase map labels extends the source map on the band; its unused values are immaterial. It can repeat labels, and outside can occur in its band image.

**Theorem 1.2 (The forced literal root and its exact rejection threshold).**

$$\forall Y \in Type,\; \forall Q \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall a \in \mathbb{N},\; \left(\left(2 \le Q \land 3 \le a\right) \land a < m\right) \Rightarrow \left(\forall alphabet \in Bool,\; \forall labels \in \operatorname{ZMod}\left(Q \cdot m + 1\right) \to Y,\; \forall outside \in Y,\; \forall rejected \in Y,\; \forall bottom \in Y,\; \left(\neg outside = rejected\right) \Rightarrow \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall pi \in \operatorname{Selector}\left(m, Y\right),\; \left(\forall history \in \operatorname{List}\left(\operatorname{AllowedBlock}\left(Q \cdot m, m, alphabet\right)\right),\; \operatorname{output}\left(Q \cdot m, \operatorname{flattenHistory}\left(history\right)\right) = \operatorname{some}\left(v\right) \Rightarrow \left(\exists budget \in \mathbb{N},\; \exists c \in \mathbb{N},\; \operatorname{execute}\left(Q \cdot m, pi, budget, \operatorname{flattenHistory}\left(history\right), \operatorname{some}\left(v\right), nil\right) = \operatorname{some}\left((\operatorname{initialLabel}\left(Q \cdot m, a, labels, outside, rejected, bottom\right)\left(\operatorname{OriginalRecord}\left(Q \cdot m, \operatorname{flattenHistory}\left(history\right)\right)\right),c)\right)\right)\right) \Rightarrow \left(\exists B \in \operatorname{Fin}\left(m\right) \to Bool,\; \exists rest \in \operatorname{List}\left(Bool\right),\; \left(\operatorname{applySelector}\left(pi, \operatorname{some}\left(v\right), nil\right) = \operatorname{inr}\left(B\right) \land \operatorname{ofFn}\left(B\right) = \operatorname{append}\left(\operatorname{replicate}\left(a, true\right), \operatorname{cons}\left(false, rest\right)\right)\right) \land \left(\forall phase \in \operatorname{ZMod}\left(Q \cdot m + 1\right),\; \forall s \in \mathbb{N},\; s < Q \cdot m \Rightarrow \operatorname{runBits}\left(Q \cdot m, B, \operatorname{some}\left(\langle v,phase,s\rangle\right)\right) = \operatorname{ifThenElse}\left(s < Q \cdot m - a, \operatorname{some}\left(\langle v + \operatorname{wordIncrement}\left(Q \cdot m, phase, B\right),phase + m,\operatorname{tailAfter}\left(0, B\right)\rangle\right), none\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.forced_threshold_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k=Qm, Q>=2 and 3<=a<m. The arbitrary Bool alphabet specifies local complete-block legality. Selector means the original adaptive selector, taking only the remembered free endpoint and the chronological acquired archive. flattenHistory concatenates each complete block's literal bits. The display suppresses positivity proof arguments in output, execute and OriginalRecord. applySelector denotes ordinary function application to its two arguments. Correctness ranges over every actual complete-block history in the selected free-value fibre, every phase, and every legal INITIAL tail. Each history has its own terminating budget; no uniform budget is assumed. It is not correctness only on a chosen initial phase.

Only outside != rejected is needed for this root clause. At phase zero, choose the two actual INITIAL tails k-a-1 and k-a with the same free value. Their labels differ. Every incorrect first-zero position erases their distinction: an earlier zero clears both tails to the same current record, while a later zero or an all-one root rejects both. Their continuations then have identical archives and records and cannot return different INITIAL labels. Joint actual-history realization supplies both records. The native paid-trace equivalence enlarges their separate terminating horizons to a common maximum without changing either returned INITIAL label or exact paid count. Thus the root must contain exactly a leading ones followed by zero.

The remaining suffix is unrestricted and the complete block has m<k bits. The first-zero execution law therefore rejects exactly s>=k-a. All lower INITIAL tails have the same terminal tail tailAfter(0,B), while scalar and phase follow the original executor. These are complete endpoint readings; the internal zero grants no intermediate observation. There is no logarithmic guard or restriction on repeated band labels.

The root law supplies the clearing step in the common-archive theorem below. It applies the first-zero acquisition, actual-history realization and execution laws to the two INITIAL tails on opposite sides of the threshold.

**Definition 1.3 (The selector's zero-reading branch).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall pi \in \operatorname{Selector}\left(m, Y\right),\; \forall v \in \operatorname{ZMod}\left(2\right),\; \operatorname{zeroArchive}\left(pi, v, 0\right) = nil \land \left(\forall t \in \mathbb{N},\; \operatorname{zeroArchive}\left(pi, v, t + 1\right) = \operatorname{append}\left(\operatorname{zeroArchive}\left(pi, v, t\right), \operatorname{list}\left((\operatorname{zeroWord}\left(pi, v, t\right),\operatorname{some}\left(v\right))\right)\right)\right)$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.zeroArchive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The archive starts empty. At each stage append the literal selected word with the successful endpoint some(v). The definition supplies a dummy all-zero word if the selector stops; the theorem proves that this alternative never occurs at any first-tour action. It is a branch definition, not an assumed legal execution.

**Definition 1.4 (The literal word on that branch).**

$$\forall Y \in Type,\; \forall m \in \mathbb{N},\; \forall pi \in \operatorname{Selector}\left(m, Y\right),\; \forall v \in \operatorname{ZMod}\left(2\right),\; \forall t \in \mathbb{N},\; \operatorname{zeroWord}\left(pi, v, t\right) = \operatorname{selectedWord}\left(\operatorname{applySelector}\left(pi, \operatorname{some}\left(v\right), \operatorname{zeroArchive}\left(pi, v, t\right)\right)\right)$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.zeroWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

selectedWord is the constructor match: inr(B) returns B, and inl(y) returns the all-false function on Fin(m). Every occurrence refers to the same selector and the same remembered free reading.

**Theorem 1.5 (The generic actual first-tour common archive).**

$$\forall Y \in Type,\; \forall Q \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall a \in \mathbb{N},\; \left(\left(2 \le Q \land 3 \le a\right) \land a < m\right) \Rightarrow \left(\forall alphabet \in Bool,\; \forall labels \in \operatorname{ZMod}\left(Q \cdot m + 1\right) \to Y,\; \forall outside \in Y,\; \forall rejected \in Y,\; \forall bottom \in Y,\; \left(\neg outside = rejected\right) \Rightarrow \left(\left(\exists p \in \operatorname{ZMod}\left(Q \cdot m + 1\right),\; \exists q \in \operatorname{ZMod}\left(Q \cdot m + 1\right),\; \left(\left(0 < \operatorname{val}\left(p\right) \land \operatorname{val}\left(p\right) < a\right) \land \left(0 < \operatorname{val}\left(q\right) \land \operatorname{val}\left(q\right) < a\right)\right) \land \left(\neg labels\left(p\right) = labels\left(q\right)\right)\right) \Rightarrow \left(\forall v \in \operatorname{ZMod}\left(2\right),\; \forall pi \in \operatorname{Selector}\left(m, Y\right),\; \left(\forall history \in \operatorname{List}\left(\operatorname{AllowedBlock}\left(Q \cdot m, m, alphabet\right)\right),\; \operatorname{output}\left(Q \cdot m, \operatorname{flattenHistory}\left(history\right)\right) = \operatorname{some}\left(v\right) \Rightarrow \left(\exists budget \in \mathbb{N},\; \exists c \in \mathbb{N},\; \operatorname{execute}\left(Q \cdot m, pi, budget, \operatorname{flattenHistory}\left(history\right), \operatorname{some}\left(v\right), nil\right) = \operatorname{some}\left((\operatorname{initialLabel}\left(Q \cdot m, a, labels, outside, rejected, bottom\right)\left(\operatorname{OriginalRecord}\left(Q \cdot m, \operatorname{flattenHistory}\left(history\right)\right)\right),c)\right)\right)\right) \Rightarrow \left(\left(\left(\forall t \in \mathbb{N},\; t < Q \Rightarrow \operatorname{applySelector}\left(pi, \operatorname{some}\left(v\right), \operatorname{zeroArchive}\left(pi, v, t\right)\right) = \operatorname{inr}\left(\operatorname{zeroWord}\left(pi, v, t\right)\right)\right) \land \left(\forall t \in \mathbb{N},\; \forall j \in \operatorname{ZMod}\left(Q \cdot m + 1\right),\; \left(t < Q \land \left(0 < \operatorname{val}\left(j\right) \land \operatorname{val}\left(j\right) < a\right)\right) \Rightarrow \operatorname{wordIncrement}\left(Q \cdot m, -j + \operatorname{cast}\left(t \cdot m\right), \operatorname{zeroWord}\left(pi, v, t\right)\right) = 0\right)\right) \land \left(\forall t \in \mathbb{N},\; \left(1 \le t \land t \le Q\right) \Rightarrow \left(\exists tail \in \mathbb{N},\; tail < Q \cdot m \land \left(\forall j \in \operatorname{ZMod}\left(Q \cdot m + 1\right),\; \forall s \in \mathbb{N},\; s < Q \cdot m - a \Rightarrow \left(\left(\forall i \in \mathbb{N},\; i < t \Rightarrow \operatorname{wordIncrement}\left(Q \cdot m, -j + \operatorname{cast}\left(i \cdot m\right), \operatorname{zeroWord}\left(pi, v, i\right)\right) = 0\right) \Rightarrow \left(\left(\exists budget \in \mathbb{N},\; \exists c \in \mathbb{N},\; \operatorname{NativeExecute}\left(pi, budget, \operatorname{some}\left(\langle v,-j + \operatorname{cast}\left(t \cdot m\right),tail\rangle\right), \operatorname{some}\left(v\right), \operatorname{zeroArchive}\left(pi, v, t\right)\right) = \operatorname{some}\left((\operatorname{initialLabel}\left(Q \cdot m, a, labels, outside, rejected, bottom\right)\left(\operatorname{some}\left(\langle v,-j,s\rangle\right)\right),c)\right)\right) \land \left(\forall history \in \operatorname{List}\left(\operatorname{AllowedBlock}\left(Q \cdot m, m, alphabet\right)\right),\; \operatorname{OriginalRecord}\left(Q \cdot m, \operatorname{flattenHistory}\left(history\right)\right) = \operatorname{some}\left(\langle v,-j,s\rangle\right) \Rightarrow \left(\operatorname{ActualArchive}\left(Q \cdot m, \operatorname{flattenHistory}\left(history\right), \operatorname{zeroArchive}\left(pi, v, t\right)\right) \land \operatorname{OriginalRecord}\left(Q \cdot m, \operatorname{append}\left(\operatorname{flattenHistory}\left(history\right), \operatorname{archiveWords}\left(\operatorname{zeroArchive}\left(pi, v, t\right)\right)\right)\right) = \operatorname{some}\left(\langle v,-j + \operatorname{cast}\left(t \cdot m\right),tail\rangle\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.first_tour_common_archive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set k=Qm. Each cast in a phase expression has codomain ZMod(k+1); all subtraction between natural numbers is truncated natural subtraction. The original target initialLabel is evaluated on the immutable INITIAL record. The same actual-history correctness premise as above permits separate terminating horizons for every history. The only band variation premise is the existence of two phases in 0<j.val<a with different labels. Other band labels can repeat and outside can occur among them. Only outside!=rejected is needed from the source's stronger separation of R from all low-tail labels. Both control alphabets and every legal inherited INITIAL tail remain included. There is no logarithmic guard.

The first conjunct proves that each of the Q words really is chosen on this one archive. The second proves zero literal response at every band phase for each such word. The third quantifies one controller-dependent current tail at each paid time 1<=t<=Q. Every low INITIAL tail at every phase whose first t literal responses are zero has its own eventually correct continuation from that same current value, phase and tail. For every actual history realizing that INITIAL record, ActualArchive and the exact OriginalRecord equation hold on that very history after appending archiveWords. Outside sources are covered by this conditional statement even when their label equals a band label. Phases remain separate coordinates and are never identified.

The root law clears all low INITIAL tails, with its arbitrary suffix determining the common terminal tail. Later first-tour windows miss the blind band. Induction transports the actual prefix equations and each source's separate eventual continuation. Two distinct band labels exclude stopping on the common archive. Phase-independent legality at a common tail excludes a uniformly rejecting selected block: its two eventual continuations would then start from the identical absorbing state and could not return distinct INITIAL labels. The remaining action is therefore actually legal for every zero-response source and advances the same archive. The native paid-trace law compares separate finite horizons without imposing one global budget.

This proves the coherent-zero-branch clause of the source theorem. The parity equivalence, actual outside survivor, attaining scan, exact support and total costs require further arguments and are not asserted here. In the even-width odd-threshold obstruction any eventual outside survivor may depend on the policy; phase m is reserved for the canonical scan's claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.first_tour_common_archive`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.forced_threshold_root`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.initialLabel`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.zeroArchive`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.zeroWord`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels](TwoAdjacentLowTailLabels.md)
