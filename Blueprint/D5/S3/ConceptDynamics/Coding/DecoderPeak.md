# Primitive decoder horizon peaks

## Abstract

The complete horizon peak bounds every retained primitive trace vertex.

The types C, I and O range independently over arbitrary universes, without finiteness or inhabitedness assumptions. The action reads only C. Frame contains the readable state together with the external acquired count and output word. Trace retains the initial state and every state reached by an internal or successful acquisition step; full(r)(q)=some(r(q)). Record is the supplied arbitrary predicate on source and input streams, and encoding is the supplied function from C to finite Boolean lists. The bound requires neither Ready nor Cut, safety, liveness, finite processing nor an injective encoding. The private trace_vertex_split constructs the intermediate Frame and actual prefix and suffix Runs; run_mono bounds its acquired count, and peak_bound includes its supplied cost in the supremum.

**Theorem 1.1 (All readable vertices belong to the complete horizon peak).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), encoding \in \operatorname{Function}\left(C, \operatorname{List}\left(Bool\right)\right), H \in Nat, a \in \operatorname{Function}\left(Nat, O\right), r \in \operatorname{Function}\left(Nat, I\right), t \in \operatorname{Frame}\left(C, O\right), vertices \in \operatorname{List}\left(C\right), c \in C,\; \left(\operatorname{Record}\left(a, r\right) \land \left(\operatorname{Trace}\left(action, \operatorname{full}\left(r\right), \operatorname{frame}\left(initial, 0, nil\right), t, vertices\right) \land \left(\operatorname{le}\left(\operatorname{acquired}\left(t\right), H\right) \land \operatorname{member}\left(c, vertices\right)\right)\right)\right) \Rightarrow \operatorname{le}\left(\operatorname{toWithTop}\left(\operatorname{length}\left(\operatorname{apply}\left(encoding, c\right)\right)\right), \operatorname{Peak}\left(action, initial, Record, encoding, H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderPeak.peak_trace_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ReachThrough(H,c) means some Record has a finite primitive run from physical initialization ending at c with acquired count at most H. Peak is the WithTop Nat supremum of the lengths of the supplied original encodings over all such states. Every trace vertex has its actual prefix run, whose acquired count is no greater than the final count. Initialization, transient workspaces, acquisition states and completed endpoints are included. Infinite peaks are retained. The encoding and its original cost are supplied rather than replaced; no equality with a maximum over chosen cut states is asserted.

**Theorem 1.2 (The complete horizon peak is monotone).**

$$\forall C \in Type, I \in Type, O \in Type, action \in \operatorname{Function}\left(C, \operatorname{Op}\left(C, I, O\right)\right), initial \in C, Record \in \operatorname{Function}\left(\operatorname{Function}\left(Nat, O\right), \operatorname{Function}\left(\operatorname{Function}\left(Nat, I\right), Prop\right)\right), encoding \in \operatorname{Function}\left(C, \operatorname{List}\left(Bool\right)\right),\; \operatorname{Monotone}\left(\operatorname{Peak}\left(action, initial, Record, encoding\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/DecoderPeak.peak_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every state reachable with at most H acquisitions is reachable with at most K whenever H <= K. Inclusion of these actual reachable states preserves the supremum bound, including infinite peaks and all original encodings.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderPeak.peak_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/DecoderPeak.peak_trace_bound`
- Dependency: [D5/S3/ConceptDynamics/Coding/DecoderOperationTrace/Basic](DecoderOperationTrace/Basic.md)
