# Native promise causal boundary

## Abstract

Every all-assignment promised comb has native causal histories and distinct legal serial orders.

C is the original ActualImageSevenLeafSeparation.E=(beta,alpha). D0 is the original FourExitRawEndpointSpectrum.z=(beta,C), and D1 is ActualImageSevenLeafSeparation.A=(C,beta). The marker is ((C,alpha),alpha), using NativeFreshSensorGrowth.cone false. promise N z is the unchanged right comb with 15N slots and that marker. Every assignment z from Fin(15N) to Bool is included; no sampled-support, group, sampler, controller or independence premise restricts the family.

Original Lean suppliers: `D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation` (E and A); `D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum` (z and comb); `D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth` (cone and original run_append); `D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair` (original context_run and D_mul).

Mathematical definitions. Bool = {false,true}; Source is the original free ordered binary-tree algebra, with of : Bool → Source and mul : Source × Source → Source; alpha = of(true), beta = of(false). For b : Bool, slot(b) is mul(C,beta) if b = true and mul(beta,C) otherwise, where C = mul(beta,alpha). The marker is mul(mul(C,alpha),alpha). For m : Source and the unique f : Fin(0) → Source, comb(0,f,m) = m. For k : Nat, f : Fin(k+1) → Source and m : Source, comb(k+1,f,m) = mul(f(0),comb(k,(i ↦ f(i+1)),m)), where i ranges over Fin(k). Thus for N : Nat and z : Fin(15N) → Bool, promise(N,z) = comb(15N,(i ↦ slot(z(i))),marker). Fin(k) = {i : Nat | i < k}, including the empty type at k = 0.

The native predicates and operations D, run, Event, erase, some, univ and the strict event order are defined in `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals`. D is the original no-left-alpha domain; run is the guarded original Call-word computation, some is successful Option output, and Event(true,t) is the full endpoint-event subtype with its induced prefix/phase order. erase maps every subtype element to its original Call without changing the list. ExtensionList(empty,univ,l) says that l lists each such event exactly once in an order with no later event below an earlier event. List(Call) contains all finite raw Call words, and ++ is concatenation. The exact recursively defined Edge and its nonreflexive finite-path closure TransGen are defined in `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder`; val forgets only event membership proofs. Every type and operation below has the same meaning as in those two native modules.

**Theorem 1.1 (All promised assignments and the causal versus serial boundary).**

$$\forall N: \mathbb{N}, ((4 \leq N) \Rightarrow (\forall z: \operatorname{Fin}\left(15 \cdot N\right) \to \operatorname{Bool}, (\begin{aligned}&\operatorname{D}\left(\operatorname{promise}\left(N, z\right)\right)\\&\land (\forall w: \operatorname{List}\left(\operatorname{Call}\right), ((\operatorname{run}\left(\operatorname{of}\left(\operatorname{true}\right), w\right) = \operatorname{some}\left(\operatorname{promise}\left(N, z\right)\right)) \iff (\exists l: \operatorname{List}\left(\operatorname{Event}\left(\operatorname{true}, \operatorname{promise}\left(N, z\right)\right)\right), ((\operatorname{erase}\left(l\right) = w) \land (\operatorname{ExtensionList}\left(\emptyset, \operatorname{univ}, l\right))))))\\&\land (\forall p: \operatorname{List}\left(\operatorname{Call}\right), (\forall q: \operatorname{List}\left(\operatorname{Call}\right), ((\operatorname{run}\left(\operatorname{of}\left(\operatorname{true}\right), p ++ q\right) = \operatorname{some}\left(\operatorname{promise}\left(N, z\right)\right)) \Rightarrow (\exists u: \operatorname{Source}, (\operatorname{run}\left(\operatorname{of}\left(\operatorname{true}\right), p\right) = \operatorname{some}\left(u\right))))))\\&\land (\forall c: \operatorname{Event}\left(\operatorname{true}, \operatorname{promise}\left(N, z\right)\right), (\forall d: \operatorname{Event}\left(\operatorname{true}, \operatorname{promise}\left(N, z\right)\right), ((\operatorname{TransGen}\left(\operatorname{Edge}\left(\operatorname{true}, \operatorname{promise}\left(N, z\right)\right), \operatorname{val}\left(c\right), \operatorname{val}\left(d\right)\right)) \iff (c < d))))\\&\land (\exists w: \operatorname{List}\left(\operatorname{Call}\right), (\exists v: \operatorname{List}\left(\operatorname{Call}\right), ((w \neq v) \land ((\operatorname{run}\left(\operatorname{of}\left(\operatorname{true}\right), w\right) = \operatorname{some}\left(\operatorname{promise}\left(N, z\right)\right)) \land (\operatorname{run}\left(\operatorname{of}\left(\operatorname{true}\right), v\right) = \operatorname{some}\left(\operatorname{promise}\left(N, z\right)\right))))))\end{aligned})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativePromiseCausalBoundary.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N at least four and every assignment z, the actual promised endpoint is in D. For every raw Call word, native success from alpha to that endpoint is equivalent to a lift to an exact labelled linear extension of its endpoint order. Every prefix of every successful word is itself a successful actual run to an intermediate source. The endpoint order is proved equal to the transitive closure of the exact local and creating-split edges. There also exist two different raw words that both succeed to this same endpoint.

The proof first verifies the original D predicate structurally on every gadget and comb. NativeEndpointEventIdeals.all_histories then gives the full raw-history characterization. Existence of a finite enabled execution is transported to an actual native run only through the proved execution_adequacy, partial_empty and cut_full; no source-specific adequacy is assumed.

For serial ambiguity, prepare a reachable comb whose first two slots are C. The zero slot insertion is promote-right then split-right; the one slot insertion is split-left then promote-right. Each is a literal two-call successful original run. Original context_run shifts these insertions into the disjoint first and second slots. Original run_append composes them in either order, producing distinct words with the same endpoint; prepending the common preparation preserves their inequality. Thus the bare endpoint supplies labelled causal information, while selecting a serial extension requires additional recipe-order data.

This is the native structural prerequisite for Unified Joint Law Bridge 5.3 and 5.6. It does not close those compound propositions, the generation-grade arithmetic, Section 3/4 actual group and partition laws, complete bounded adaptive controller measurability, the exact eight-event signed law, or common full-tree submass. No theorem about unconditional adaptive independence or recovery of a serial clock from a bare endpoint is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativePromiseCausalBoundary.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](../FourExitRawEndpointSpectrum.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder](NativeEndpointCausalOrder.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation](../ActualImageSevenLeafSeparation.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](../FourExitRawEndpointSpectrum.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder](NativeEndpointCausalOrder.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals](NativeEndpointEventIdeals.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth](NativeFreshSensorGrowth.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair](NativeGuardedLeafRepair.md)
