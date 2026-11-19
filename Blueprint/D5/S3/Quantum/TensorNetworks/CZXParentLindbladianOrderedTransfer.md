# Finite-time CZX evolution and ordered transfer

## Abstract

The finite-time CZX evolution and its fixed-time trace-distance estimate.

**Definition 1.1 (Cyclic middle pairs).**

$$\forall (m: \mathbb{N}), (\forall (x: (\operatorname{Fin}\left((2) \cdot (m)\right)) \to (\operatorname{Fin}\left(2\right))), (\forall (k: \operatorname{Fin}\left(m\right)), (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.blocks}\left(m, x, k\right) = \operatorname{Prod.mk}\left(x\left(\operatorname{Fin.ofNat}\left((2) \cdot (m), ((2) \cdot (\operatorname{Fin.val}\left(k\right))) + (1)\right)\right), x\left(\operatorname{Fin.ofNat}\left((2) \cdot (m), ((2) \cdot (\operatorname{Fin.val}\left(k\right))) + (2)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.blocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

At index k the block records sites 2k+1 and 2k+2 modulo the ring length. The last block ends at site zero.

**Definition 1.2 (Initial operator).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.initial}\left(m\right) = (\frac{1}{(4)^{m}}) \cdot ((1) + (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel.tensorX}\left((2) \cdot (m)\right))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The identity plus the global spin flip has normalization 4 to the power minus m.

**Definition 1.3 (Stationary operator).**

$$\forall (m: \mathbb{N}), (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.stationary}\left(m\right) = (\frac{1}{(4)^{m}}) \cdot ((1) + (((2) \cdot (\frac{1}{(2)^{m}})) \cdot (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel.czxUnitary}\left((2) \cdot (m)\right)))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.stationary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The same normalization multiplies the identity and the CZX symmetry operator weighted by 2 to the power 1−m.

**Definition 1.4 (Canonical trace distance).**

$$\forall (m: \mathbb{N}), (\forall (t: \mathbb{R}), (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.delta}\left(m, t\right) = \frac{\operatorname{D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm}\left((\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel.evolution}\left((2) \cdot (m), t, \operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.initial}\left(m\right)\right)) - (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.stationary}\left(m\right))\right)}{2}))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The readout is half the trace norm of the difference of the actual evolved operator and the stationary operator.

**Theorem 1.5 (Exact ordered transfer).**

$$\forall (m: \mathbb{N}), ((2 \le m) \Rightarrow (\forall (t: \mathbb{R}), (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel.evolution}\left((2) \cdot (m), t, \operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.initial}\left(m\right)\right) = (\frac{1}{(4)^{m}}) \cdot ((1) + ((\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianWindowChannel.czxUnitary}\left((2) \cdot (m)\right)) \cdot (\operatorname{Matrix.diagonal}\left(\lambda (x: (\operatorname{Fin}\left((2) \cdot (m)\right)) \to (\operatorname{Fin}\left(2\right))) \mapsto (\operatorname{Complex.ofReal}\left(((\frac{1}{2})^{m}) \cdot (\operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth.word}\left(\operatorname{Real.exp}\left(-t\right), m, \operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.blocks}\left(m, x\right)\right)\right))\right))\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.evolved_initial_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The original exponential factors over all even starts. On the weighted gauge sector the factors independently refresh the cyclic middle pairs. Summing the second bit of each pair gives the literal transfer letter. Contraction around the cycle traces the product in increasing block order. Both starts on a four-site ring occur in the factorization.

**Theorem 1.6 (Fixed-time quantum bound).**

$$\forall (m: \mathbb{N}), ((2 \le m) \Rightarrow (\forall (t: \mathbb{R}), ((0 < t) \Rightarrow (\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianOrderedTransfer.delta}\left(m, t\right) \le (2) \cdot ((\frac{\operatorname{D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAnnealedGrowth.growthFactor}\left(\operatorname{Real.exp}\left(-t\right)\right)}{2})^{m})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.fixed_time_delta_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yuhan Liu; Alberto Ruiz-de-Alarcón; Georgios Styliaris; Xiao-Qi Sun; David Pérez-García; J. Ignacio Cirac (2026). *Parent Lindbladians for matrix product density operators*. DOI: [10.1103/1qyd-59z7](https://doi.org/10.1103/1qyd-59z7). URL: <https://arxiv.org/abs/2501.10552v2>.

*Commentary.*

The unitary factor in the evolved difference gives singular values equal to the absolute diagonal coefficients. Centering the resulting word traces subtracts two. Each diagonal entry is bounded by the Euclidean norm of its corresponding row. Applying annealed growth to both coordinate rows yields the displayed bound. For positive time the growth factor divided by two is strictly below one.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.blocks`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.delta`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.evolved_initial_transfer`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.fixed_time_delta_upper`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.initial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/CZXParentLindbladianOrderedTransfer.stationary`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FuchsLogarithmBasisRefutation](../Foundation/FuchsLogarithmBasisRefutation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth](CZXParentLindbladianAnnealedGrowth.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/CZXParentLindbladianSteadyState](CZXParentLindbladianSteadyState.md)
