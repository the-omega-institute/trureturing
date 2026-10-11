# Primitive decoder operations

## Abstract

Finite actual operation traces preserve original readable states, emitted batches and acquisition boundaries.

**Theorem 1.1 (An actual acquired run contains finite startup).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, r \in \operatorname{Function}\left(Nat, I\right), t \in \operatorname{Frame}\left(C, O\right),\; \left(\operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), t\right) \land \operatorname{lt}\left(0, \operatorname{acquired}\left(t\right)\right)\right) \Rightarrow \left(\exists u \in \operatorname{Frame}\left(C, O\right),\; \operatorname{Drain}\left(action, \operatorname{frame}\left(initial, 0, nil\right), u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.initial_drain_of_acquired_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite Run whose acquired count is positive contains a first acquisition. Its preceding retained prefix consists solely of internal operations and ends at the actual acquire state. Transfer to the empty available input gives a Drain from physical initialization. Every prefix vertex is retained; neither global computation bounds nor termination on unreachable states are required.

**Theorem 1.2 (Actual first-label competitors derive startup from the recovery contract).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), InD \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), Prop\right), a \in \operatorname{Function}\left(Nat, O\right), beta \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), otherInput \in \operatorname{Function}\left(Nat, I\right),\; \left(\operatorname{Safety}\left(action, initial, Record\right) \land \left(\operatorname{Liveness}\left(action, initial, Record, InD\right) \land \left(\operatorname{Record}\left(a, r\right) \land \left(\operatorname{Record}\left(beta, otherInput\right) \land \left(\operatorname{InD}\left(a\right) \land \left(\operatorname{notEqual}\left(\operatorname{apply}\left(a, 0\right), \operatorname{apply}\left(beta, 0\right)\right) \land \left(\forall source \in \operatorname{Function}\left(Nat, O\right), input \in \operatorname{Function}\left(Nat, I\right), c \in C, d \in C, q \in Nat, outword \in \operatorname{List}\left(O\right), batch \in \operatorname{List}\left(O\right), f \in \operatorname{Function}\left(I, \operatorname{Option}\left(\operatorname{Product}\left(C, \operatorname{List}\left(O\right)\right)\right)\right),\; \left(\operatorname{Record}\left(source, input\right) \land \left(\operatorname{Run}\left(action, \operatorname{full}\left(input\right), \operatorname{frame}\left(initial, 0, nil\right), \operatorname{frame}\left(c, q, outword\right)\right) \land \left(\operatorname{apply}\left(action, c\right) = \operatorname{acquire}\left(f\right) \land \operatorname{apply}\left(f, \operatorname{apply}\left(input, q\right)\right) = \operatorname{some}\left(\operatorname{pair}\left(d, batch\right)\right)\right)\right)\right) \Rightarrow \left(\exists t \in \operatorname{Frame}\left(C, O\right),\; \operatorname{Drain}\left(action, \operatorname{frame}\left(d, \operatorname{add}\left(q, 1\right), \operatorname{append}\left(outword, batch\right)\right), t\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Processing}\left(action, initial, Record\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.processing_of_safe_live_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Safety and Liveness have exactly the all-Record finite-run and positionwise InD meanings displayed above. The two supplied actual records have different first source labels; only the first needs InD liveness. Its live first output cannot occur with zero acquisitions, since the same internal prefix transfers to the competitor and safety would equate their first labels. The acquired run therefore supplies finite startup. Processing then follows from that derived drain and the displayed drains after every actual successful acquisition. Post-acquisition finiteness is not inferred from safety alone. Original complete-readable-state and instruction correspondence remains a separate semantic assessment.

**Theorem 1.3 (Unread suffix replay with independent old output).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), r \in \operatorname{Function}\left(Nat, I\right), s \in \operatorname{Frame}\left(C, O\right), t \in \operatorname{Frame}\left(C, O\right), vertices \in \operatorname{List}\left(C\right),\; \operatorname{Trace}\left(action, \operatorname{full}\left(r\right), s, t, vertices\right) \Rightarrow \left(\exists m \in Nat, w \in \operatorname{List}\left(O\right),\; \operatorname{acquired}\left(t\right) = \operatorname{add}\left(\operatorname{acquired}\left(s\right), m\right) \land \left(\operatorname{output}\left(t\right) = \operatorname{append}\left(\operatorname{output}\left(s\right), w\right) \land \left(\forall otherInput \in \operatorname{Function}\left(Nat, I\right), otherOffset \in Nat, otherOutput \in \operatorname{List}\left(O\right),\; \left(\forall j \in Nat,\; \operatorname{apply}\left(r, \operatorname{add}\left(\operatorname{acquired}\left(s\right), j\right)\right) = \operatorname{apply}\left(otherInput, \operatorname{add}\left(otherOffset, j\right)\right)\right) \Rightarrow \operatorname{Trace}\left(action, \operatorname{full}\left(otherInput\right), \operatorname{frame}\left(\operatorname{state}\left(s\right), otherOffset, otherOutput\right), \operatorname{frame}\left(\operatorname{state}\left(t\right), \operatorname{add}\left(otherOffset, m\right), \operatorname{append}\left(otherOutput, w\right)\right), vertices\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.trace_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Op has internal(next,batch), acquire(input to Option(next,batch)), and stopped. Step has only the two original internal and successful available acquisition rules. Frame consists of the original readable state and external acquired count and output word. action reads only the state. Trace retains its entire state vertex list and every finite edge batch. full(r)(q)=some(r(q)). Replay preserves that vertex list exactly, accumulates the actual acquisition and output increments, and changes neither state identity nor batches. Offset and old-output changes are external bookkeeping. Partial acquisition and unreachable loops remain allowed.

**Theorem 1.4 (Position liveness supplies every actual D cut).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), InD \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), Prop\right), a \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), n \in Nat,\; \left(\operatorname{Processing}\left(action, initial, Record\right) \land \left(\operatorname{Liveness}\left(action, initial, Record, InD\right) \land \left(\operatorname{Record}\left(a, r\right) \land \operatorname{InD}\left(a\right)\right)\right)\right) \Rightarrow \left(\exists t \in \operatorname{Frame}\left(C, O\right),\; \operatorname{Cut}\left(action, initial, \operatorname{front}\left(r, n\right), t\right) \land \operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.actual_cut_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ready means acquire or stopped. A Cut is a finite trace over the available front(r,n), from the physical initial state with acquired zero and empty output, ending Ready at acquired n. No End event is supplied. Processing means a finite internal-only startup drain and a finite internal-only drain after every acquisition actually executed on any Record. It quantifies neither over unreachable states nor impossible acquisitions. Liveness means every position has a finite full-run witness for every Record in InD. Startup gives n=0. Deterministic path comparability and liveness beyond the current finite output force the next acquisition; its actual drain supplies the next cut. This is an explicit operational theorem. Universal correspondence to a prose machine definition, endpoint granularity require independent assessment; finite startup is derived from actual first-label competitors by processing_of_safe_live_pair.

**Theorem 1.5 (Live actual addresses agree after equal-state replay).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), InD \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), Prop\right), a \in \operatorname{Function}\left(Nat, O\right), b \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), otherInput \in \operatorname{Function}\left(Nat, I\right), s \in \operatorname{Frame}\left(C, O\right), otherCut \in \operatorname{Frame}\left(C, O\right),\; \left(\operatorname{Safety}\left(action, initial, Record\right) \land \left(\operatorname{Liveness}\left(action, initial, Record, InD\right) \land \left(\operatorname{Record}\left(a, r\right) \land \left(\operatorname{Record}\left(b, otherInput\right) \land \left(\operatorname{InD}\left(a\right) \land \left(\operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), s\right) \land \left(\operatorname{Run}\left(action, \operatorname{full}\left(otherInput\right), \operatorname{frame}\left(initial, 0, nil\right), otherCut\right) \land \left(\operatorname{state}\left(s\right) = \operatorname{state}\left(otherCut\right) \land \left(\operatorname{output}\left(s\right) = \operatorname{output}\left(otherCut\right) \land \left(\forall j \in Nat,\; \operatorname{apply}\left(r, \operatorname{add}\left(\operatorname{acquired}\left(s\right), j\right)\right) = \operatorname{apply}\left(otherInput, \operatorname{add}\left(\operatorname{acquired}\left(otherCut\right), j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow a = b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.actual_address_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Safety means that on every Record every emitted position in every finite primitive run equals its source address. Liveness is positionwise and restricted to InD. Equal cut states, equal cumulative words and one equal unread suffix imply address equality: choose a liveness witness beyond both the requested position and old output, compare actual paths, replay the continuation, and apply safety on both records. No replay or joint injection is a premise.

**Theorem 1.6 (All readable vertices belong to the complete horizon peak).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), encoding \in \operatorname{Function}\left(C, \operatorname{List}\left(Bool\right)\right), H \in Nat, a \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), t \in \operatorname{Frame}\left(C, O\right), vertices \in \operatorname{List}\left(C\right), c \in C,\; \left(\operatorname{Record}\left(a, r\right) \land \left(\operatorname{Trace}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), t, vertices\right) \land \left(\operatorname{le}\left(\operatorname{acquired}\left(t\right), H\right) \land \operatorname{member}\left(c, vertices\right)\right)\right)\right) \Rightarrow \operatorname{le}\left(\operatorname{toWithTop}\left(\operatorname{length}\left(\operatorname{apply}\left(encoding, c\right)\right)\right), \operatorname{Peak}\left(action, initial, Record, encoding, H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.peak_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ReachThrough(H,c) means some Record has a finite primitive run from physical initialization ending at c with acquired count at most H. Peak is the WithTop Nat supremum of the lengths of the supplied original encodings over all such states. Every trace vertex has its actual prefix run, whose acquired count is no greater than the final count. Initialization, transient workspaces, acquisition states and completed endpoints are included. Infinite peaks are retained. The encoding and its original cost are supplied rather than replaced; no equality with a maximum over chosen cut states is asserted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.actual_address_eq`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.actual_cut_exists`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.initial_drain_of_acquired_run`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.peak_trace_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.processing_of_safe_live_pair`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.trace_replay`
