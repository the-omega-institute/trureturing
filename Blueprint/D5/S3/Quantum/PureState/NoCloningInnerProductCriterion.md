# No-Cloning Inner-Product Criterion

## Abstract

Exact unitary cloning makes the input-state overlap idempotent.

**Theorem 1.1 (Clonable pure states are identical or orthogonal).**

$$\forall H \in Type, U \in LinearIsometryEquiv\left(\mathbb{C}, TensorProduct\left(\mathbb{C}, H, H\right), TensorProduct\left(\mathbb{C}, H, H\right)\right), psi \in H, phi \in H, blank \in H,\; NormedAddCommGroup\left(H\right) \land InnerProductSpace\left(\mathbb{C}, H\right) \land \Vert psi \Vert = 1 \land \Vert phi \Vert = 1 \land \Vert blank \Vert = 1 \land U\left(tmul\left(\mathbb{C}, psi, blank\right)\right) = tmul\left(\mathbb{C}, psi, psi\right) \land U\left(tmul\left(\mathbb{C}, phi, blank\right)\right) = tmul\left(\mathbb{C}, phi, phi\right) \Rightarrow \langle phi, psi \rangle_{\mathbb{C}} = \langle phi, psi \rangle_{\mathbb{C}}^{2} \land (phi = psi \lor \langle phi, psi \rangle_{\mathbb{C}} = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/NoCloningInnerProductCriterion.no_cloning_inner_product_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex linear isometric equivalence is assumed to clone two normalized vectors from the same normalized blank vector.

Preservation of the tensor-product inner product makes their overlap equal to its square. Unit overlap identifies the normalized vectors, while the remaining idempotent value is zero.

## References

- Truth anchor: `D5/S3/Quantum/PureState/NoCloningInnerProductCriterion.no_cloning_inner_product_criterion`
