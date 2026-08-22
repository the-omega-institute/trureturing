# Coordinate Residue Bilayer Is Not a Product

## Abstract

A three-point bilayer decomposes into dependent coordinate fibers but not into a uniform product; uniform fiber equivalences suffice for a product decomposition.

**Theorem 1.1 (Unequal coordinate residues obstruct a uniform product).**

$$\operatorname{Nonempty}\left(BilayerObject \equiv \sum _{b: Bool} \operatorname{ConceptFiber}\left(bilayerConcept, b\right)\right) \land \forall R: \operatorname{Type}, \neg \operatorname{Nonempty}\left(BilayerObject \equiv Bool \times R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/CoordinateResidueBilayerNotProduct.coordinate_residue_bilayer_not_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The false coordinate carries one residual point, while the true coordinate carries two. Their dependent sum therefore has three points, and reading the coordinate gives its canonical dependent-fiber decomposition.

A hypothetical product with the two-point Boolean coordinate would have twice as many points as its residue type. Finiteness of that residue follows from the hypothetical equivalence, so its product cannot have the bilayer's odd cardinality of three.

**Lemma 1.2 (Uniform residues yield a product decomposition).**

$$\forall X, B, R: \operatorname{Type}, q: X \to B, {\forall b: B, \operatorname{ConceptFiber}\left(q, b\right) \equiv R} \Rightarrow \operatorname{Nonempty}\left(X \equiv B \times R\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/CoordinateResidueBilayerNotProduct.product_decomposition_of_uniform_residues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every fiber of a readout is equipped with an equivalence to one fixed residue type. These equivalences assemble the dependent sum of the fibers into the ordinary product of the coordinate and residue types.

Composing this assembly with the canonical dependent-fiber decomposition recovers the source as that product. The condition needs no finiteness assumption and isolates a sufficient uniformity condition absent from the bilayer counterexample.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/CoordinateResidueBilayerNotProduct.coordinate_residue_bilayer_not_product`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/CoordinateResidueBilayerNotProduct.product_decomposition_of_uniform_residues`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
