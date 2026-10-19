# Primitive decoder trace foundations

## Abstract

Finite primitive traces retain actual readable states and acquisition boundaries.

**Theorem 1.1 (Position liveness supplies every actual D cut).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), InD \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), Prop\right), a \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), n \in Nat,\; \left(\operatorname{Processing}\left(action, initial, Record\right) \land \left(\operatorname{Liveness}\left(action, initial, Record, InD\right) \land \left(\operatorname{Record}\left(a, r\right) \land \operatorname{InD}\left(a\right)\right)\right)\right) \Rightarrow \left(\exists t \in \operatorname{Frame}\left(C, O\right),\; \operatorname{Cut}\left(action, initial, \operatorname{front}\left(r, n\right), t\right) \land \operatorname{Run}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace/Basic.actual_cut_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ready means acquire or stopped. A Cut is a finite trace over the available front(r,n), from the physical initial state with acquired zero and empty output, ending Ready at acquired n. No End event is supplied. Processing means a finite internal-only startup drain and a finite internal-only drain after every acquisition actually executed on any Record. It quantifies neither over unreachable states nor impossible acquisitions. Liveness means every position has a finite full-run witness for every Record in InD. Startup gives n=0. Deterministic path comparability and liveness beyond the current finite output force the next acquisition; its actual drain supplies the next cut. This is an explicit operational theorem. Universal correspondence to a prose machine definition, endpoint granularity require independent assessment; finite startup is derived from actual first-label competitors by processing_of_safe_live_pair.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderOperationTrace/Basic.actual_cut_exists`
- Dependency: [D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral](../FibonacciFactorCompletion/Bilateral.md)
