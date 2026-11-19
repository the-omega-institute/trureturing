# Affine Two-Readout Normalization

## Abstract

An affine equation for two translates of a bounded group function determines a common offset.

**Theorem 1.1 (The coefficient at a non-involutive step).**

$$\forall G \in Type,\; \operatorname{Group}\left(G\right) \Rightarrow \left(\forall p \in G \to \mathbb{R},\; \left(\forall g \in G,\; p\left(g^{-1}\right) = p\left(g\right)\right) \Rightarrow \left(\left(\forall g \in G,\; \forall h \in G,\; p\left(h \cdot g \cdot h^{-1}\right) = p\left(g\right)\right) \Rightarrow \left(\left(\forall g \in G,\; p\left(g\right) = 1 \Leftrightarrow g = 1\right) \Rightarrow \left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall u \in G,\; \left(\forall z \in G,\; p\left(z \cdot u^{-1}\right) = a \cdot p\left(z\right) + b \cdot p\left(z \cdot u\right) + d\right) \Rightarrow \left(u \cdot u \ne 1 \Rightarrow b = -1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization.coefficient_eq_neg_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the one-sided law at the step and its inverse gives two equations. Their difference shows that one plus the forward coefficient annihilates the difference between the readout at the square and the identity. Faithfulness makes that difference nonzero.

**Theorem 1.2 (Normalization of the symmetric affine law).**

$$\forall G \in Type,\; \operatorname{Group}\left(G\right) \Rightarrow \left(\forall p \in G \to \mathbb{R},\; p\left(1\right) = 1 \Rightarrow \left(\left(\forall g \in G,\; p\left(g^{-1}\right) = p\left(g\right)\right) \Rightarrow \left(\left(\forall g \in G,\; \forall h \in G,\; p\left(h \cdot g \cdot h^{-1}\right) = p\left(g\right)\right) \Rightarrow \left(\left(\forall g \in G,\; \left|p\left(g\right)\right| \le 1\right) \Rightarrow \left(\left(\exists g \in G,\; p\left(g\right) \ne 1\right) \Rightarrow \left(\forall a \in G \to \mathbb{R},\; \forall d \in G \to \mathbb{R},\; \left(\forall z \in G,\; \forall u \in G,\; p\left(z \cdot u\right) + p\left(z \cdot u^{-1}\right) = a\left(u\right) \cdot p\left(z\right) + d\left(u\right)\right) \Rightarrow \left(\exists m \in \mathbb{R},\; m < 1 \land \left(\left(\forall g \in G,\; \left|\frac{p\left(g\right) - m}{1 - m}\right| \le 1\right) \land \left(\forall z \in G,\; \forall u \in G,\; \frac{p\left(z \cdot u\right) - m}{1 - m} + \frac{p\left(z \cdot u^{-1}\right) - m}{1 - m} = 2 \cdot \frac{p\left(z\right) - m}{1 - m} \cdot \frac{p\left(u\right) - m}{1 - m}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization.bounded_dalembert_of_affine_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The group is arbitrary. Centrality and invariance under inversion let the two arguments of the symmetric readout exchange roles. Evaluation at the identity then ties the two coefficient functions to one common offset. If the linear coefficient were always two, the defect from one would grow under squaring, contradicting boundedness. The normalized equation gives duplication, which both forces the offset below one and bounds the normalized function between minus one and one.

**Theorem 1.3 (The one-sided law when only the identity squares to the identity).**

$$\forall G \in Type,\; \operatorname{Group}\left(G\right) \Rightarrow \left(\forall p \in G \to \mathbb{R},\; \left(\forall g \in G,\; p\left(g^{-1}\right) = p\left(g\right)\right) \Rightarrow \left(\left(\forall g \in G,\; \forall h \in G,\; p\left(h \cdot g \cdot h^{-1}\right) = p\left(g\right)\right) \Rightarrow \left(\left(\forall g \in G,\; p\left(g\right) = 1 \Leftrightarrow g = 1\right) \Rightarrow \left(\left(\forall g \in G,\; \left|p\left(g\right)\right| \le 1\right) \Rightarrow \left(\left(\exists g \in G,\; p\left(g\right) \ne 1\right) \Rightarrow \left(\left(\forall u \in G,\; u \cdot u = 1 \Rightarrow u = 1\right) \Rightarrow \left(\left(\forall u \in G,\; u \ne 1 \Rightarrow \left(\exists a \in \mathbb{R},\; \exists b \in \mathbb{R},\; \exists d \in \mathbb{R},\; \forall z \in G,\; p\left(z \cdot u^{-1}\right) = a \cdot p\left(z\right) + b \cdot p\left(z \cdot u\right) + d\right)\right) \Rightarrow \left(\exists m \in \mathbb{R},\; m < 1 \land \left(\left(\forall g \in G,\; \left|\frac{p\left(g\right) - m}{1 - m}\right| \le 1\right) \land \left(\forall z \in G,\; \forall u \in G,\; \frac{p\left(z \cdot u\right) - m}{1 - m} + \frac{p\left(z \cdot u^{-1}\right) - m}{1 - m} = 2 \cdot \frac{p\left(z\right) - m}{1 - m} \cdot \frac{p\left(u\right) - m}{1 - m}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization.bounded_dalembert_of_one_sided_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every nonidentity step, faithfulness forces the forward coefficient to be minus one. The identity step already has a symmetric law with linear coefficient two and offset zero. The symmetric normalization therefore applies to the entire group.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization.bounded_dalembert_of_affine_law`
- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization.bounded_dalembert_of_one_sided_law`
- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/TwoReadoutNormalization.coefficient_eq_neg_one`
- Dependency: [D5/S3/Analytic/Dilation/DuplicationCircleRigidity](../../../Analytic/Dilation/DuplicationCircleRigidity.md)
