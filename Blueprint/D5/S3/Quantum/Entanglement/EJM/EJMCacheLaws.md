# Actual local-action and block-projection laws

## Abstract

Actual local-action and block-projection laws

Small finite kernel receipts check both inverse directions, coordinate multiplication, common-outcome composition and the original-block incidence tables. Symbolic function proofs then derive exact update and composition laws for arbitrary original partial assignments. The coordinate composition order is preserved rather than inferred from a producer tag. These laws are consumed by full cache association proofs.

**Theorem 1.1 (Triangle coordinate actions are injective).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_coordinate_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_coordinate_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the checked inverse to equality of two transformed coordinates recovers equality of the original coordinates for every one of the twelve actual triangle permutations.

**Theorem 1.2 (Singleton coordinate actions are injective).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_coordinate_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_coordinate_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same inverse argument proves injectivity for all twelve actual singleton coordinate permutations.

**Theorem 1.3 (The triangle preimage returns the original coordinate).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_preimage_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_preimage_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every full local symmetry and triangle coordinate, applying its actual coordinate action to the recorded preimage returns that coordinate.

**Theorem 1.4 (The singleton preimage returns the original coordinate).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_preimage_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_preimage_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checked singleton right inverse supplies the exact coordinate recovery needed to transport arbitrary fills.

**Theorem 1.5 (Exact composition on the whole triangle partial event).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_compose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_compose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Option-map composition and actual coordinate/outcome function equalities prove that applying t after s equals the recorded composed action on every coordinate.

**Theorem 1.6 (Exact composition on the whole singleton partial event).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_compose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_compose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the same symbolic whole-function proof for the actual singleton coordinate tables.

**Theorem 1.7 (Transport an actual triangle coordinate fill).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_update`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Injectivity and the actual right inverse show that a fill at i becomes a fill at the preimage of i, with its value transformed by the existing outcome action. Other coordinates retain the full old partial assignment.

**Theorem 1.8 (Transport an actual singleton coordinate fill).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_update`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The update proof uses the actual singleton inverse and outcome action. It applies to arbitrary partial assignments, with no normalization or producer premise.

**Theorem 1.9 (Triangle actions preserve an unknown at its preimage).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_unknown`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_unknown` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an original triangle partial assignment is unknown at a coordinate, the transformed assignment is unknown at its actual preimage. Exact coordinate recovery and Option.map prove this without restricting the other coordinates.

**Theorem 1.10 (Singleton actions preserve an unknown at its preimage).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_unknown`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_unknown` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unknown singleton coordinate remains unknown at its actual preimage under the full coordinate and outcome action.

**Theorem 1.11 (A triangle incidence names the actual global coordinate).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_incidence_some`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_incidence_some` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whenever the original incidence table returns local coordinate i for global coordinate g and placement k, the actual triangle placement sends i to g.

**Theorem 1.12 (A singleton incidence names the actual global coordinate).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_incidence_some`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_incidence_some` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every some-entry in the original singleton incidence table agrees with the actual singleton placement map.

**Theorem 1.13 (Exact change in an original triangle block).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_projection_update`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_projection_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A checked some-incidence and original block injectivity identify the single changed local coordinate. A checked none-incidence proves that the whole original projection is unchanged.

**Theorem 1.14 (Exact change in an original singleton block).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_projection_update`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_projection_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual singleton map receives the same complete projection proof, retaining every original coordinate and value.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_compose`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_coordinate_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_incidence_some`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_preimage_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_projection_update`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_unknown`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.singleton_update`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_compose`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_coordinate_injective`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_incidence_some`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_preimage_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_projection_update`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_unknown`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.triangle_update`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData](EJMLocalCacheData.md)
