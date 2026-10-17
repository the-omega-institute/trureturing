# Critical complete storage

## Abstract

Actual unbounded return counts give an all-horizon lower bound for complete primitive states.

The original paired sources share one positive return list, the fixed length-twenty-six stem, and their prescribed high and low tails. Every list is supplied at the critical budget for each of the closed, strict and individual-record-margin error contracts. A record margin exists because nonzero errors have finite departure support; no common positive margin is assumed.

The exact critical budget for the whole fixed-tail family

Let ActualCosts contain the closed-cell cost of each actual departure of either prescribed original source, for every finite positive Return list, including empty. Every member is strictly below lam. On the high singleton [Return(1,R)], the actual color-1 departure 30 has cost d_R=lam-g^2*chi^R*X_H. These costs tend to lam as R tends to infinity, so sSup(ActualCosts)=lam and lam is not attained by a finite slot.

Every fixed legal ownership supplies the family at lam for the closed, strict and record-margin contracts. Conversely, for every b<lam and every contract, some positive R makes the high history of [Return(1,R)] impossible: the actual slot cost exceeds b. Therefore lam is the minimum feasible budget for each of the three contracts. Taking b=lam-epsilon rules out every common positive family margin epsilon. Each finite record still has its own positive margin, since its finitely many departure errors are strictly below lam and its remaining prescribed future uses zero error.

Remaining full-decoder requirements

The fixed-tail boundary and the complete primitive-state lower bound do not close the full decoder result. A universal representation of every Definition 36.9 decoder in the primitive model remains required, together with the actual online construction of 33.13: safety on all Omega sources; liveness on every D source, including empty windows; finite primitive updates; and full O(N+1) readable memory accounting for history, DFS, current reference words, control, counters, positions, timing and output-side state. These are separate from the length-counting applications and do not follow from budget sharpness. No lower-coefficient optimality is asserted.

**Theorem 1.1 (Complete primitive storage bound).**

$$\forall Configuration \in Type, action \in Configuration \to \operatorname{Op}\left(Configuration, Color, Label\right), initialConfiguration \in Configuration, o \in Ownership, contract \in Contract, encoding \in Configuration \to \operatorname{List}\left(Bool\right),\; \left(\operatorname{Processing}\left(action, initialConfiguration, \operatorname{OperationRecord}\left(o, lam, contract\right)\right) \land \left(\left(\forall a \in Nat \to Label, r \in Nat \to Color,\; \operatorname{OperationRecord}\left(o, lam, contract, a, r\right) \Rightarrow \left(\forall t \in \operatorname{Frame}\left(Configuration, Label\right),\; \operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initialConfiguration, 0, \operatorname{nil}\left(Label\right)\right), t\right) \Rightarrow \left(\forall p \in Nat,\; \operatorname{lt}\left(p, \operatorname{length}\left(\operatorname{output}\left(t\right)\right)\right) \Rightarrow \operatorname{getElem}\left(\operatorname{output}\left(t\right), p\right) = \operatorname{apply}\left(a, p\right)\right)\right)\right) \land \left(\left(\forall a \in Nat \to Label, r \in Nat \to Color,\; \left(\operatorname{OperationRecord}\left(o, lam, contract, a, r\right) \land \operatorname{OperationFiniteSource}\left(a\right)\right) \Rightarrow \left(\forall p \in Nat,\; \exists t \in \operatorname{Frame}\left(Configuration, Label\right),\; \operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initialConfiguration, 0, \operatorname{nil}\left(Label\right)\right), t\right) \land \operatorname{lt}\left(p, \operatorname{length}\left(\operatorname{output}\left(t\right)\right)\right)\right)\right) \land \operatorname{InjOn}\left(encoding, \operatorname{setOf}\left((c : Configuration \mapsto \exists H \in Nat,\; \operatorname{ReachThrough}\left(action, initialConfiguration, \operatorname{OperationRecord}\left(o, lam, contract\right), H, c\right))\right)\right)\right)\right)\right) \Rightarrow \left(\forall N \in Nat, B \in Nat,\; \operatorname{le}\left(\operatorname{Peak}\left(action, initialConfiguration, \operatorname{OperationRecord}\left(o, lam, contract\right), encoding, N\right), \operatorname{toWithTopNat}\left(B\right)\right) \Rightarrow \operatorname{le}\left(\operatorname{subtract}\left(\operatorname{subtract}\left(\operatorname{multiply}\left(alphaInfinity, \operatorname{toReal}\left(N\right)\right), \operatorname{multiply}\left(107, alphaInfinity\right)\right), 1\right), \operatorname{toReal}\left(B\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedCriticalStorage.critical_decoder_storage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Configuration is the complete readable primitive state. Processing must terminate at each actual acquisition; safety holds on every actual legal source record, and liveness supplies every position on every eventually-zero source. The encoding is injective on all reachable complete states. Intermediate workspace, readable control, counters, positions, timing and output-side data belong to the state. Frame acquisition and output fields are proof bookkeeping and provide no input to the action.

At checkpoint twenty-six plus twice n, the same first future and empty past output separate all returnCount n sources. Binary strings of length at most B have capacity two to the B plus one minus one. For horizons at least eighty-eight, take n equal to the floor of N minus twenty-six divided by two. The count estimate loses eighty alpha, the stem twenty-six alpha, parity at most one alpha, and variable-length coding one bit. Nonnegative storage handles smaller horizons. A peak of infinity is permitted; the implication applies whenever the peak has a finite bound.

The theorem concerns the stated primitive-operation model. A representation of every prose decoder in this model and the original closed-observation online upper construction are separate requirements. The lower bound alone establishes neither an optimal coefficient nor a matching memory order.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedCriticalStorage.critical_decoder_storage`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount](UnboundedReturnCount.md)
