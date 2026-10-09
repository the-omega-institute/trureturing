# Compatible Raw Cache Fibers

## Abstract

Compatible raw cache fibers retain every nominal branch or absent lift over a coarse history.

A coarse history retains literal addresses, order, repetitions and the coarse reply. For each coarse-none entry both raw branch and raw absent remain available; alpha and beta are forced by their Boolean labels. The fiber represents every raw history with that projection. It becomes an ordered first-occurrence cache when the address list has no duplicates, as proved for every coarse prefix used by the pure acquisition compiler. No source-realizability predicate removes nominal ghost lifts.

**Definition 1.1 (Literal coarse histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.CoarseHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.CoarseHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CoarseHistory is List (Sigma (fun _ : Address => Option Bool)).

**Definition 1.2 (Full raw reply fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.ReplyLift`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.ReplyLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ReplyLift z contains every original Reply y satisfying kappa y equals z. The none fiber contains branch and absent; each Boolean-label fiber has one element.

**Definition 1.3 (Compatible cache fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.CompatCache`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.CompatCache` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CompatCache g is the product of the raw reply lifts at every position of g.

**Definition 1.4 (Raw cache decoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

decode keeps every address, raw reply and order in a compatible cache.

**Theorem 1.5 (Coarse projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding a compatible cache and applying kappa_hist returns exactly its coarse history.

**Theorem 1.6 (Fiber injectivity).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two compatible cache fibers with the same coarse history and decoded raw history are equal.

**Theorem 1.7 (Fiber completeness).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every raw history with coarse projection g is represented by a compatible cache in the fiber.

**Definition 1.8 (Exact raw history packing).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.pack`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.pack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any raw history h whose projection equals g, pack g h embeds that literal history into CompatCache g.

**Theorem 1.9 (Packing preserves raw values).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_pack`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_pack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding a packed history returns exactly the input h, including every raw value and its position.

**Definition 1.10 (Exact fiber bijection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.cacheEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.cacheEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

cacheEquiv identifies CompatCache g with the full inverse image of g under kappa_hist. Its inverse is pack, justified by completeness and injective decoding.

**Theorem 1.11 (Exact compatible count).**

$$\forall g: CoarseHistory, \operatorname{card}\left(\operatorname{CompatCache}\left(g\right)\right) = 2^{\operatorname{noneCount}\left(g\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.compatible_cache_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty fiber has one element. Every none entry contributes the two original branch and absent lifts; each labelled entry contributes one. Induction multiplies these independent factors and yields the exact nominal fiber count, without filtering inconsistent or unrealized histories.

**Theorem 1.12 (Address preservation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_addresses`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_addresses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoded cache addresses are exactly the coarse history addresses.

**Definition 1.13 (Coarse-none count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.noneCount`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.noneCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

noneCount counts coarse entries whose reply is none.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.CoarseHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.CompatCache`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.ReplyLift`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.cacheEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.compatible_cache_card`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_addresses`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_injective`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_pack`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_projection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.decode_surjective`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.noneCount`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/ActualAcquisitionCacheFiber.pack`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverAbsorbingNormalization](ActualObserverAbsorbingNormalization.md)
