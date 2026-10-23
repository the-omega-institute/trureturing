# Primitive decoder replay and source addresses

## Abstract

Unread suffix replay preserves primitive traces and identifies safe live source addresses.

The types C, I and O range independently over arbitrary universes, without finiteness or inhabitedness assumptions. Run means that some finite Trace joins the given Frames. Initialization is the Frame with state initial, acquired count zero and empty output. Safety(action,initial,Record) means that for every source a and input r satisfying Record(a,r), every finite Run from initialization on full(r), and every natural position p below its output length, the emitted symbol at p equals a(p). Liveness(action,initial,Record,InD) means that for every such Record with InD(a) and every natural position p, some finite Run from initialization on full(r) emits more than p symbols. In the address formula, s and otherCut denote arbitrary reachable Frames: the phrase equal cut states refers to their equal readable states, and neither Ready nor Cut is required. Only a must satisfy InD; the acquired counts need not coincide.

**Theorem 1.1 (Unread suffix replay with independent old output).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), r \in \operatorname{Function}\left(Nat, I\right), s \in \operatorname{Frame}\left(C, O\right), t \in \operatorname{Frame}\left(C, O\right), vertices \in \operatorname{List}\left(C\right),\; \operatorname{Trace}\left(action, \operatorname{full}\left(r\right), s, t, vertices\right) \Rightarrow \left(\exists m \in Nat, w \in \operatorname{List}\left(O\right),\; \operatorname{acquired}\left(t\right) = \operatorname{add}\left(\operatorname{acquired}\left(s\right), m\right) \land \left(\operatorname{output}\left(t\right) = \operatorname{append}\left(\operatorname{output}\left(s\right), w\right) \land \left(\forall otherInput \in \operatorname{Function}\left(Nat, I\right), otherOffset \in Nat, otherOutput \in \operatorname{List}\left(O\right),\; \left(\forall j \in Nat,\; \operatorname{apply}\left(r, \operatorname{add}\left(\operatorname{acquired}\left(s\right), j\right)\right) = \operatorname{apply}\left(otherInput, \operatorname{add}\left(otherOffset, j\right)\right)\right) \Rightarrow \operatorname{Trace}\left(action, \operatorname{full}\left(otherInput\right), \operatorname{frame}\left(\operatorname{state}\left(s\right), otherOffset, otherOutput\right), \operatorname{frame}\left(\operatorname{state}\left(t\right), \operatorname{add}\left(otherOffset, m\right), \operatorname{append}\left(otherOutput, w\right)\right), vertices\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderReplay.trace_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Op has internal(next,batch), acquire(input to Option(next,batch)), and stopped. Step has only the two original internal and successful available acquisition rules. Frame consists of the original readable state and external acquired count and output word. action reads only the state. Trace retains its entire state vertex list and every finite edge batch. full(r)(q)=some(r(q)). Replay preserves that vertex list exactly, accumulates the actual acquisition and output increments, and changes neither state identity nor batches. Offset and old-output changes are external bookkeeping. Partial acquisition and unreachable loops remain allowed.

**Theorem 1.2 (Live actual addresses agree after equal-state replay).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), InD \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), Prop\right), a \in \operatorname{Function}\left(Nat, O\right), b \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), otherInput \in \operatorname{Function}\left(Nat, I\right), s \in \operatorname{Frame}\left(C, O\right), otherCut \in \operatorname{Frame}\left(C, O\right),\; \left(\operatorname{Safety}\left(action, initial, Record\right) \land \left(\operatorname{Liveness}\left(action, initial, Record, InD\right) \land \left(\operatorname{Record}\left(a, r\right) \land \left(\operatorname{Record}\left(b, otherInput\right) \land \left(\operatorname{InD}\left(a\right) \land \left(\operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), s\right) \land \left(\operatorname{Run}\left(action, \operatorname{full}\left(otherInput\right), \operatorname{frame}\left(initial, 0, nil\right), otherCut\right) \land \left(\operatorname{state}\left(s\right) = \operatorname{state}\left(otherCut\right) \land \left(\operatorname{output}\left(s\right) = \operatorname{output}\left(otherCut\right) \land \left(\forall j \in Nat,\; \operatorname{apply}\left(r, \operatorname{add}\left(\operatorname{acquired}\left(s\right), j\right)\right) = \operatorname{apply}\left(otherInput, \operatorname{add}\left(\operatorname{acquired}\left(otherCut\right), j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow a = b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderReplay.actual_address_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Safety means that on every Record every emitted position in every finite primitive run equals its source address. Liveness is positionwise and restricted to InD. Equal cut states, equal cumulative words and one equal unread suffix imply address equality: choose a liveness witness beyond both the requested position and old output, compare actual paths, replay the continuation, and apply safety on both records. No replay or joint injection is a premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderReplay.actual_address_eq`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderReplay.trace_replay`
- Dependency: [D5/S3/ConceptDynamics/Coding/DecoderOperationTrace/Basic](DecoderOperationTrace/Basic.md)
