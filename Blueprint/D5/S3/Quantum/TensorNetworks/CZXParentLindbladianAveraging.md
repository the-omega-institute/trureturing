# CZX coordinate averaging

## Abstract

Commuting coordinate averages on finite binary configurations.

**Definition 1.1 (The coordinate average).**

$$\forall (V: Type), [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\mathbb{C}, V\right)], \forall (n: \mathbb{N}), \forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, s\right) = \operatorname{Finset}.{noncommProd}\left(s, \lambda (k: \operatorname{Fin}\left(n\right)) \mapsto (\lambda (f: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (V)) \mapsto (\lambda (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto ((((2: \mathbb{C}))^{-1}) \cdot (\sum_{b: \operatorname{Fin}\left(2\right)} f\left(\operatorname{Function}.{update}\left(x, k, b\right)\right)))))\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Avg is the noncommutative product of the commuting binary-coordinate averaging endomorphisms over a finite set of sites.

**Theorem 1.2 (The empty average).**

$$\forall (V: Type), [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\mathbb{C}, V\right)], \forall (n: \mathbb{N}), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, \operatorname{Finset}.{empty}\left(\right)\right) = (1: \operatorname{Module}.{End}\left(\mathbb{C}, ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (V)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The average over no coordinates is the identity endomorphism.

**Theorem 1.3 (Multiplication of averages).**

$$\forall (V: Type), [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\mathbb{C}, V\right)], \forall (n: \mathbb{N}), \forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (t: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, s\right)) \cdot (\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, t\right)) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, \operatorname{Finset}.{union}\left(s, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the averages over two finite site sets gives the average over their union, using idempotence and commutation of the coordinate averages.

**Theorem 1.4 (Commutation of averages).**

$$\forall (V: Type), [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\mathbb{C}, V\right)], \forall (n: \mathbb{N}), \forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (t: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{Commute}\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, s\right), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Averages over arbitrary finite site sets commute because every coordinate average commutes with every other one.

**Theorem 1.5 (A two-coordinate average).**

$$\forall (V: Type), [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\mathbb{C}, V\right)], \forall (n: \mathbb{N}), \forall (k: \operatorname{Fin}\left(n\right)), \forall (l: \operatorname{Fin}\left(n\right)), (k \ne l) \Rightarrow (\forall (f: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (V)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, \operatorname{Finset}.{insert}\left(k, \operatorname{Finset}.{singleton}\left(l\right)\right)\right)\left(f\right)\left(x\right) = (((4: \mathbb{C}))^{-1}) \cdot (\sum_{b: \operatorname{Fin}\left(2\right)} \sum_{c: \operatorname{Fin}\left(2\right)} f\left(\operatorname{Function}.{update}\left(\operatorname{Function}.{update}\left(x, k, b\right), l, c\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_pair_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct sites k and l, applying the average over their pair gives the four equally weighted updates of the two coordinates.

**Theorem 1.6 (Averages commute with linear maps).**

$$\forall (V: Type), [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\mathbb{C}, V\right)], \forall (W: Type), [\operatorname{AddCommGroup}\left(W\right)], [\operatorname{Module}\left(\mathbb{C}, W\right)], \forall (n: \mathbb{N}), \forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), \forall (l: \operatorname{LinearMap}\left(\mathbb{C}, V, W\right)), \forall (f: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (V)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), l\left(\operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, s\right)\left(f\right)\left(x\right)\right) = \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, s\right)\left(\lambda (y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (l\left(f\left(y\right)\right))\right)\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex-linear map can be moved through a coordinate average by map-additivity, map-scalar multiplication, and induction over the finite product.

**Theorem 1.7 (The full coordinate average).**

$$\forall (V: Type), [\operatorname{AddCommGroup}\left(V\right)], [\operatorname{Module}\left(\mathbb{C}, V\right)], \forall (n: \mathbb{N}), \forall (f: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))) \to (V)), \forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))), \operatorname{D5}.{S3}.{Quantum}.{TensorNetworks}.{CZXParentLindbladianAveraging}.{avg}\left(n, \operatorname{Finset}.{univ}\left(\right)\right)\left(f\right)\left(x\right) = ((((2)^{n}: \mathbb{C}))^{-1}) \cdot (\sum_{y: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(2\right))} f\left(y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Averaging over every site gives the uniform average over all binary configurations, with normalization two to the power n.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_commute`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_empty`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_map`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_mul`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_pair_apply`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAveraging.avg_univ`
