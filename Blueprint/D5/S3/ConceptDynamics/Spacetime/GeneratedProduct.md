# Archive-Preserving Generated Product

## Abstract

Archive-Preserving Generated Product.

**Definition 1.1 (Only generated pairs are current or selected).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The archive retains the two tagged old archives and every pair of current parents under the third tag. All generated candidate pairs form the new current region. Selection uses only selected parent pairs; old events never contribute again merely by being archived.

**Theorem 1.2 (Selected and background sums multiply exactly).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.q_product`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.q_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected readout is the actual signed double sum and equals the product of input readouts. The same calculation on full current regions gives the background product and balanced closure. The archive has E-left plus E-right plus Omega-left times Omega-right events.

**Definition 1.3 (Both old archives embed with all attributes and order).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.embeddingLeft`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.embeddingLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit tagged injections preserve all four attributes and preserve and reflect old causality. The path invariant and frozen path-mapping theorem occur on the proof path. No nonzero-readout or nonempty-current assumption is needed.

**Theorem 1.4 (HF causality has the required finite path semantics).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.causal_iff_bounded_path`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.causal_iff_bounded_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transported causal relation equals actual TransGen of the two copied relations and the two parent edges on HF members. Its paths are characterized by positive relation-series lengths bounded by archive cardinality minus one.

**Theorem 1.5 (Archive retention does not recover old selections).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product_eq_of_empty_right`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product_eq_of_empty_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two selections on each fixed input context, an empty opposite current region makes the product results equal. The symmetric theorem handles an empty left region. The result retains old archives, without claiming recovery of prior selections or current regions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.causal_iff_bounded_path`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.embeddingLeft`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.product_eq_of_empty_right`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct.q_product`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths](FiniteCausalPaths.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ProductPaths](ProductPaths.md)
