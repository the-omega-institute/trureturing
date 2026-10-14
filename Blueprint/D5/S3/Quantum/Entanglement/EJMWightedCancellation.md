# Weighted inflation cancellation

## Abstract

Exact weighted cancellation for transformed triangle inflation identities.

**Theorem 1.1 (Finite factor cancellation).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.finite_weighted_block_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMWightedCancellation.finite_weighted_block_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite A and B, a block mass p(a)k(b) can be summed against any coefficient F by first contracting the A coordinate.

**Theorem 1.2 (Integer-scale cancellation).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.finite_scaled_weighted_block_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMWightedCancellation.finite_scaled_weighted_block_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact denominator and score scales cancel the contracted target block. This is the algebraic consumer of the continuous inflation marginal identity.

**Theorem 1.3 (Preserve B,A,C export order).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.triangle_mass_in_BAC_order`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMWightedCancellation.triangle_mass_in_BAC_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A marginal map whose tuple is ordered B,A,C is interpreted using the actual party-labelled A,B,C arguments; no hidden-law symmetry is assumed.

**Theorem 1.4 (B singleton marginal).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.singleton_mass_in_B_order`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMWightedCancellation.singleton_mass_in_B_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The B singleton contributes the explicit sum over A and C outcomes.

**Theorem 1.5 (Actual tuple expectation).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_expectation_tuple`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_expectation_tuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective tuple of observed nodes and its complement reindex the full finite law. Summing the complement yields the actual continuous-response marginal, so every tuple score has the same expectation under that marginal.

**Theorem 1.6 (Independent centered block).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_centered_expectation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_centered_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disjoint actual source supports and a proven head marginal give zero expectation of the scaled head-and-tail score after exact target contraction.

**Theorem 1.7 (Preserve finite export indexing).**

Lean statement: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_centered_fin_expectation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_centered_fin_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The consumed adapter preserves the original Fin(m+n) coefficient order when separating its first m outcomes from its remaining n outcomes.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.finite_scaled_weighted_block_cancellation`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.finite_weighted_block_cancellation`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_centered_expectation`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_centered_fin_expectation`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.inflation_expectation_tuple`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.singleton_mass_in_B_order`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJMWightedCancellation.triangle_mass_in_BAC_order`
- Dependency: [D5/S3/Quantum/Entanglement/TriangleInflationSoundness](TriangleInflationSoundness.md)
