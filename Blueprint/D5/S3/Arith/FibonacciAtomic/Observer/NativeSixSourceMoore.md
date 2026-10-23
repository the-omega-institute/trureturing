# Three Calls Force Ten Total States

## Abstract

Constant complete entry and three stationary native calls require five running states and five disjoint whole-row halting states on the original repeated-partner inverse fiber.

The comparison domain is the entire infinite OriginFiber(P,row) from NativeSixSourceCones. It contains every finite origin whose one-step image has the exact complete depth-three row with classes a,b1,a,b2,c,b3,c,b4 and all cross-class disequalities. The six fixed actual origins from that module are a restriction used only in the lower proof. The native interface still permits every finite address and all four replies.

A controller has arbitrary finite types Q and H. Its complete state is their disjoint sum. Every member of Q has one fixed literal address and four fixed successor entries. Every member of H has one fixed complete LiteralRow output. All tables are common to every source. All states, including unused states, are counted. A halt consumes no invocation. Each running visit consumes exactly one invocation, including repeated visits, deep addresses and absence. A mathematical Run trace records those visits for the proof and is not additional accessible controller storage. Shared states, merging histories, cycles across runs, early halts and halting entry states are permitted.

**Theorem 1.1 (Full-Fiber State Obstruction).**

$$\forall Q: Type, (\forall H: Type, ([\operatorname{Fintype}\left(Q\right)] [\operatorname{Fintype}\left(H\right)], \forall M: \operatorname{Controller}\left(Q, H\right), (\forall entry: \operatorname{Sum}\left(Q, H\right), ((\forall x: Fiber, (\exists h: H, (\exists tr: \operatorname{List}\left(Q\right), ((\operatorname{Run}\left(M, \operatorname{rho}\left(x\right), entry, tr, h\right)) \land (\operatorname{out}\left(M, h\right) = \operatorname{canonicalRow}\left(P, x\right)) \land (\operatorname{length}\left(tr\right) \leq 3))))) \implies ((5 \leq \operatorname{card}\left(Q\right)) \land (5 \leq \operatorname{card}\left(H\right)) \land (10 \leq \operatorname{card}\left(\operatorname{Sum}\left(Q, H\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceMoore.three_call_state_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive right class, compare its actual positive source with the zero source having the same partner beta placement. Their questions agree at every location except that right class. Equal replies along one terminating run reproduce the same terminal state on the other source. Distinct complete predecessor rows exclude that outcome, forcing one actual state at each of the four right-cone locations.

Suppose no running state has a partner-cone address. Compare the zero-a run with each positive source. On that run only the corresponding positive right cone can separate each pair. Thus all four distinct right-cone locations must occur along the same zero-a run. Its list of running visits has length at most three, a contradiction. A fifth running state therefore has a partner-cone address. The five address locations are disjoint, so their required states are different regardless of shared histories or cycles.

The five pairwise different canonical predecessor rows require five different terminal states, because the whole output is fixed at each halt. Cardinal monotonicity on the disjoint state sum gives ten total states. The entry variable is one fixed complete mutable state, expressing the constant-export case after the supplied complete-entry normalization. Acquisition, genuine same-version data, actual export, authenticated update continuity, recoverable entry and the complete access cut remain supplied premises. No output decoder, inverse operation or physical storage/time equivalence is provided.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceMoore.three_call_state_obstruction`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones](NativeSixSourceCones.md)
