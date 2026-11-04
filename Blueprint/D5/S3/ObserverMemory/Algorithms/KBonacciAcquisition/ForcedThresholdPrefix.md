# Forced arbitrary tail thresholds

## Abstract

An immutable INITIAL tail threshold forces the first zero of every correct literal root.

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

This statement establishes the root clause of the forced-prefix theorem. It does not assert the common first-tour archive, the parity obstruction, an attaining scan, exact surviving phase support, or any total cost formula.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.forced_threshold_root`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/ForcedThresholdPrefix.initialLabel`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels](TwoAdjacentLowTailLabels.md)
