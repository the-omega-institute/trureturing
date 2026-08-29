# Memory Transport

## Abstract

Sequential memory transport along concatenated action words composes.

**Theorem 1.1 (Transport along concatenated words composes).**

$$\forall first, second: \operatorname{List}\left((M \to M)\right), m: M, \operatorname{transportWord}\left(first ++ second, m\right) = \operatorname{transportWord}\left(second, \operatorname{transportWord}\left(first, m\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/MemoryTransport.transportWord_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A transport word is a finite list of memory endomorphisms executed from left to right.

Executing first ++ second at a memory state equals executing first and then executing second from the resulting memory.

**Theorem 1.2 (The empty word has trivial transport).**

$$\forall m: M, \operatorname{transportWord}\left([], m\right) = m.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/MemoryTransport.transportWord_nil` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty update list performs no memory transformation.

Its transport therefore returns every input memory state unchanged.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/MemoryTransport.transportWord_append`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/MemoryTransport.transportWord_nil`
