# Scale38 Raw Endpoint Spectrum

## Abstract

Raw endpoint addresses and leaf-response obstructions for the nested compensation family.

The nested compensation family is indexed by one baseline member and two finite-index rows. The existing Scale38 query addresses provide the left comb scan.

**Definition 1.1 (Peeling endpoint predicate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.rawEndpoint`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.rawEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A native family member is a raw endpoint when its transported finite family admits a Peels list from the full survivor set.

**Theorem 1.2 (Equal leaf replies obstruct peeling).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.no_peel_of_leaf_agreement`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.no_peel_of_leaf_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two distinct competitors differ from the target and agree at every target leaf, then no safe raw peeling list can delete both competitors. A nonleaf response group would contain both members, while a matching response keeps both in the survivor set.

**Theorem 1.3 (Row certificates determine all target leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.leaf_agreement_of_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.leaf_agreement_of_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every labelled row belonging to a target gives the same reply for two competitors, the complete frontier and response table imply equality of their replies at every leaf of that target.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.leaf_agreement_of_rows`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.no_peel_of_leaf_agreement`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38RawEndpointSpectrum.rawEndpoint`
- Dependency: [D5/S3/Arith/FibonacciAtomic/RawEndpointPeeling](RawEndpointPeeling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38LeafFrontierResponse](Scale38LeafFrontierResponse.md)
