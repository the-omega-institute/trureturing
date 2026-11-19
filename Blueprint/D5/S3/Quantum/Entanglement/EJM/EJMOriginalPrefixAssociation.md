# Association of each original prefix cache and partial assignment

## Abstract

Association of each original prefix cache and partial assignment

The prefix has twenty coordinates with four values each. Its cache starts with the original thirty-two local states and applies the same base-four digits as the partial assignment. Depth distinguishes leading zero values. Every natural code is allowed; only the lowest depth digits participate.

**Definition 1.1 (Coordinate at a prefix depth).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.coordinate`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At depth d the coordinate is d modulo twenty. The two theorems restrict the prefix depth to at most twenty, so no assigned coordinate is revisited.

**Definition 1.2 (Cache after the original prefix).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixCache`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixCache` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth zero uses the original initial cache. At depth d+1, apply the cache step at coordinate d to the cache for code divided by four, using code modulo four as the next outcome.

**Definition 1.3 (Partial assignment after the same prefix).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixPartial`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixPartial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth zero leaves every coordinate unassigned. The successor updates the same coordinate with the same outcome as prefixCache.

**Theorem 1.4 (Future coordinates remain unassigned).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixPartial_future_none`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixPartial_future_none` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every depth at most twenty, every natural code and every coordinate whose value is at least that depth, prefixPartial returns none. Depth induction keeps the next coordinate distinct from each future coordinate.

**Theorem 1.5 (The cache represents the same complete prefix).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefix_associated`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefix_associated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every depth at most twenty and every natural code, prefixCache and prefixPartial satisfy AssociatedCache. The proof starts with initial_associated and applies step_associated at the previously unassigned coordinate. It does not assume a bound on the code.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.coordinate`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixCache`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixPartial`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefixPartial_future_none`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalPrefixAssociation.prefix_associated`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness](EJMCacheSoundness.md)
