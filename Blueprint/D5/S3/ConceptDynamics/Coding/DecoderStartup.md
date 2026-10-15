# Finite decoder startup

## Abstract

Finite actual acquisition and first-label competitors determine decoder startup.

Op consists of internal(next,batch), acquire(input to Option(next,batch)), and stopped. A Frame records a readable state, an external acquired count and an output word; action reads only the state. A finite Run uses internal steps and successful available acquisitions, retaining every intermediate state. The full input has full(r)(q)=some(r(q)). Ready means stopped or acquire. A Drain is a finite Run with no available input ending Ready, so every step is internal. Processing requires a Drain at initialization and after each actually successful acquisition on any Record. The types C, I and O range independently over arbitrary universes; no finiteness or inhabitedness assumption is imposed.

**Theorem 1.1 (An actual acquired run contains finite startup).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, r \in \operatorname{Function}\left(Nat, I\right), t \in \operatorname{Frame}\left(C, O\right),\; \left(\operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), t\right) \land \operatorname{lt}\left(0, \operatorname{acquired}\left(t\right)\right)\right) \Rightarrow \left(\exists u \in \operatorname{Frame}\left(C, O\right),\; \operatorname{Drain}\left(action, \operatorname{frame}\left(initial, 0, nil\right), u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderStartup.initial_drain_of_acquired_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite Run whose acquired count is positive contains a first acquisition. Its preceding retained prefix consists solely of internal operations and ends at the actual acquire state. Transfer to the empty available input gives a Drain from physical initialization. Every prefix vertex is retained; neither global computation bounds nor termination on unreachable states are required.

**Theorem 1.2 (Actual first-label competitors derive startup from the recovery contract).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), InD \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), Prop\right), a \in \operatorname{Function}\left(Nat, O\right), beta \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), otherInput \in \operatorname{Function}\left(Nat, I\right),\; \left(\operatorname{Safety}\left(action, initial, Record\right) \land \left(\operatorname{Liveness}\left(action, initial, Record, InD\right) \land \left(\operatorname{Record}\left(a, r\right) \land \left(\operatorname{Record}\left(beta, otherInput\right) \land \left(\operatorname{InD}\left(a\right) \land \left(\operatorname{notEqual}\left(\operatorname{apply}\left(a, 0\right), \operatorname{apply}\left(beta, 0\right)\right) \land \left(\forall source \in \operatorname{Function}\left(Nat, O\right), input \in \operatorname{Function}\left(Nat, I\right), c \in C, d \in C, q \in Nat, outword \in \operatorname{List}\left(O\right), batch \in \operatorname{List}\left(O\right), f \in \operatorname{Function}\left(I, \operatorname{Option}\left(\operatorname{Product}\left(C, \operatorname{List}\left(O\right)\right)\right)\right),\; \left(\operatorname{Record}\left(source, input\right) \land \left(\operatorname{Run}\left(action, \operatorname{full}\left(input\right), \operatorname{frame}\left(initial, 0, nil\right), \operatorname{frame}\left(c, q, outword\right)\right) \land \left(\operatorname{apply}\left(action, c\right) = \operatorname{acquire}\left(f\right) \land \operatorname{apply}\left(f, \operatorname{apply}\left(input, q\right)\right) = \operatorname{some}\left(\operatorname{pair}\left(d, batch\right)\right)\right)\right)\right) \Rightarrow \left(\exists t \in \operatorname{Frame}\left(C, O\right),\; \operatorname{Drain}\left(action, \operatorname{frame}\left(d, \operatorname{add}\left(q, 1\right), \operatorname{append}\left(outword, batch\right)\right), t\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Processing}\left(action, initial, Record\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderStartup.processing_of_safe_live_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Safety means that for every Record(a,r), every finite Run from initialization on full(r), and every p below its output length, the emitted symbol at p equals a(p). Liveness means that for every Record(a,r) with InD(a) and every natural position p, some finite Run on full(r) emits more than p symbols. The two supplied actual records have different first source labels; only the first needs InD liveness. Its live first output cannot occur with zero acquisitions, since the same internal prefix transfers to the competitor and safety would equate their first labels. The acquired run therefore supplies finite startup. Processing then follows from that derived drain and the displayed drains after every actual successful acquisition. Post-acquisition finiteness is not inferred from safety alone. The state C must contain all readable memory, and action must describe the actual internal and acquisition instructions for this operational model to represent a physical decoder.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderStartup.initial_drain_of_acquired_run`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderStartup.processing_of_safe_live_pair`
- Dependency: [D5/S3/ConceptDynamics/Coding/DecoderOperationTrace](DecoderOperationTrace.md)
