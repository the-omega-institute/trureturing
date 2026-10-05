# Exact ordered power products

## Abstract

Products use the original ordered list, with exactly m factors and without a commutativity assumption.

**Definition 1.1 (The exact power-product set).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.orderedPowerProducts`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.orderedPowerProducts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any group G and natural q and m, orderedPowerProducts(G,q,m) is the range of powerProduct q m on functions from Fin m to G. The latter multiplies the qth powers in the order of List.finRange m. Identity factors and repetitions are allowed; m equal to zero gives only the identity.

**Lemma 1.2 (Identity padding).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.one_mem_orderedPowerProducts`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.one_mem_orderedPowerProducts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group G and every natural q and m, the identity belongs to orderedPowerProducts(G,q,m). Choose the identity in every coordinate, including the empty list.

**Lemma 1.3 (Lift each factor through a surjection).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.lift_orderedPowerProducts`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.lift_orderedPowerProducts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any surjective group homomorphism f from G to Q and natural q and m, each x in orderedPowerProducts(Q,q,m) has a preimage y in orderedPowerProducts(G,q,m). Choose a lift of each of the exact m factors and apply map_powerProduct. Multiplication order and length are preserved.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.lift_orderedPowerProducts`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.one_mem_orderedPowerProducts`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.orderedPowerProducts`
- Dependency: [D5/S3/Factorization/Galois/ProfinitePowerTransfer](../../Factorization/Galois/ProfinitePowerTransfer.md)
