# Leaf Source Square Readout

## Abstract

Equal-leaf source filtering of the actual generated history gives a finite square sum.

**Definition 1.1 (Selection filtering preserves the complete context).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.sourceFilter`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.sourceFilter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition 13 permits any fixed set of source trees. The filter changes only the selected events, retaining the identical archive, current region, attributes and causal data. The balanced lift reuses the input balance proof.

**Theorem 1.2 (One finitely supported charge records signed source fibers).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.source_charge_apply`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.source_charge_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The charge is the finite sum of signed singletons over actual selected occurrences. Its coefficient is the full signed event-fiber sum and the singleton-filter readout. A zero coefficient can still have a nonempty occurrence fiber.

**Theorem 1.3 (The generated history contains every ordered selected parent pair).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_product_fiber_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_product_fiber_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed filter admits precisely pairs of equal leaf sources. Complete occurring fibers are grouped before any zero total is discarded. Distinct occurrences with the same leaf source contribute cross terms; equal nonleaf sources are excluded.

**Theorem 1.4 (The actual readout equals the leaf-source square sum).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem consumes both representation equalities and finite distributivity. It holds for every balanced history in dimension three, including empty selections and signed cancellation, without positivity or per-source balance assumptions.

**Theorem 1.5 (Natural leaf indices reindex the same finite sum).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout_nat`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Natural leaf charges are derived from the one source charge by restriction and precomposition. Restriction to leaves precedes the support bijection. This establishes only the readout identity in Proposition 68.1, with no syntax-membership, separation, whole-CSA or ZFC conservativity or consistency claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_product_fiber_readout`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout_nat`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.sourceFilter`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.source_charge_apply`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/GeneratedProduct](GeneratedProduct.md)
