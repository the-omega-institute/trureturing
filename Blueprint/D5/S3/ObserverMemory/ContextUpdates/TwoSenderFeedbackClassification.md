# Two-Sender Feedback Classification

## Abstract

One binary broadcast classifies two simultaneous binary replies on the complete modulo-four source.

**Definition 1.1 (The original source and its kernel-valued clock offset).**

Lean statement: `D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification.sourceEquiv`

*Formalization.* `D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification.sourceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write Z4 = ZMod 4 and Z2 = ZMod 2. The characteristic chi is reduction modulo two. The source (a,u,v,h) in Z4 cubed times Z2 corresponds bijectively to ((a,[u,v]),2h) in the generic Source with two labelled senders and offset in ker chi. The inverse reads the two sender coordinates and returns h=0 for offset zero, h=1 for offset two. The generic target is Y=a+u+v and its clock is t=Y+2h.

**Theorem 1.2 (All exact protocols have one shared affine parameter family).**

$$\forall P \in \operatorname{Protocol}(\operatorname{ZMod}(4), \operatorname{Fin}(2), Bool, \operatorname{Const}(Bool)), D \in \operatorname{ZMod}(4) \to \left(\operatorname{ZMod}(4) \to \left(Bool \to \left(Bool \to \left(Bool \to \operatorname{ZMod}(4)\right)\right)\right)\right),\; \operatorname{Correct}(P, D) \Leftrightarrow \left(\exists c \in \operatorname{ZMod}(4) \to Bool, A \in \operatorname{ZMod}(4) \to \left(Bool \to Bool\right), B \in \operatorname{ZMod}(4) \to \left(Bool \to Bool\right), cTwo \in \operatorname{ZMod}(4) \to \left(Bool \to Bool\right), cThree \in \operatorname{ZMod}(4) \to \left(Bool \to Bool\right),\; \left(\left(\left(\left(\left(\left(\forall a \in \operatorname{ZMod}(4), t \in \operatorname{ZMod}(4),\; \operatorname{query}(P, a, t) = \operatorname{xor}(\operatorname{low}(t - a), c(t))\right) \land \left(\forall t \in \operatorname{ZMod}(4), p \in Bool,\; \operatorname{xor}(A(t, p), B(t, p)) = \operatorname{xor}(true, p)\right)\right) \land \left(\forall t \in \operatorname{ZMod}(4), b \in Bool, u \in \operatorname{ZMod}(4),\; \operatorname{reply}(P, 0, u, t, b) = \operatorname{xor}(\operatorname{xor}(\operatorname{high}(u), \operatorname{mul}(A(t, \operatorname{xor}(b, c(t))), \operatorname{low}(u))), cTwo(t, \operatorname{xor}(b, c(t))))\right)\right) \land \left(\forall t \in \operatorname{ZMod}(4), b \in Bool, v \in \operatorname{ZMod}(4),\; \operatorname{reply}(P, 1, v, t, b) = \operatorname{xor}(\operatorname{xor}(\operatorname{high}(v), \operatorname{mul}(B(t, \operatorname{xor}(b, c(t))), \operatorname{low}(v))), cThree(t, \operatorname{xor}(b, c(t))))\right)\right) \land \left(\forall a \in \operatorname{ZMod}(4), t \in \operatorname{ZMod}(4), b \in Bool, r \in Bool, s \in Bool,\; \operatorname{Actual}(P, a, t, b, r, s) \Rightarrow D(a, t, b, r, s) = a + \operatorname{bit}(\operatorname{xor}(b, c(t))) + 2 \cdot \operatorname{bit}(\operatorname{xor}(\operatorname{xor}(\operatorname{xor}(\operatorname{xor}(r, s), cTwo(t, \operatorname{xor}(b, c(t)))), cThree(t, \operatorname{xor}(b, c(t)))), \operatorname{mul}(B(t, \operatorname{xor}(b, c(t))), \operatorname{xor}(b, c(t)))))\right)\right) \land \left(\forall t \in \operatorname{ZMod}(4), b \in Bool,\; \exists a \in \operatorname{ZMod}(4), r \in Bool, s \in Bool,\; \operatorname{Actual}(P, a, t, b, r, s)\right)\right) \land \left(\forall a \in \operatorname{ZMod}(4), t \in \operatorname{ZMod}(4), r \in Bool, s \in Bool,\; \operatorname{Actual}(P, a, t, \operatorname{query}(P, a, t), r, s)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P has an arbitrary deterministic query q(a,t) and two arbitrary deterministic binary reply maps e(u,t,b) and f(v,t,b), indexed zero and one in Protocol. Const(Bool) is the constant Boolean reply-type family. The receiver broadcasts b=q(a,t) before the two replies are sent simultaneously. Each reply depends only on its sender coordinate, the clock and the broadcast. D is any deterministic decoder on (a,t,b,r,s). Source coordinates remain fixed during this exchange.

L(x) and H(x) are the low and high bits of the standard representative of x. xor denotes Boolean exclusive-or, mul denotes Boolean multiplication, and bit embeds false as zero and true as one in Z4. All additions in the decoder formula take place in Z4. Correct(P,D) requires D to return Y for every original source. Actual(P,a,t,b,r,s) means some source has receiver a, clock t, broadcast b and the two indicated replies.

The displayed existential binds one c and one family A,B,cTwo,cThree for all inputs at once. The two reply equations hold for every local input, including both broadcasts. The decoder equation is imposed only when Actual holds. Both broadcast labels occur at every clock, and all four reply pairs occur at every receiver and clock. Consequently the actual image consists exactly of b=q(a,t) with arbitrary r and s; the decoder is unrestricted elsewhere.

Exact recovery on the reachable parity fibre and separation within each characteristic fibre follow from `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_decoder` and `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.fiber_separated_of_branch_exact`. Boolean separation gives the affine forms of the local replies.

For each prescribed reply pair, choose the high bits separately at both low-bit assignments. These two sources have the same observation. Their decoded totals must agree, forcing the coefficient relation. One broadcast branch therefore cannot serve different parities of t-a. Both parities exist and there are only two broadcast labels, so q(a,t)=xor(L(t-a),q(t,t)). Set c(t)=q(t,t) and read the reply constants and slopes at inputs zero and one in branch xor(p,c(t)). This same choice gives all the displayed equations and reachability claims.

Conversely the coefficient relation cancels the low-bit term in the sum of the two reconstructed coordinates. The imposed decoder value then equals a+u+v for each source. This argument uses no restriction on the decoder outside the actual image.

## References

- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.branch_exact_of_decoder`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification.fiber_separated_of_branch_exact`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification.result`
- Truth anchor: `D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification.sourceEquiv`
- Dependency: [D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification](ExactSnapshotCollisionClassification.md)
