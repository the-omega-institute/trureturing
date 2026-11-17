# MRD density: Tensor

## Abstract

Fixed-field MRD density: tensor argument.

**Definition 1.1 (Rectangle).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] \forall F \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(F\right)] [\operatorname{Module}\left(K, F\right)] \forall U \in \operatorname{Submodule}\left(K, E\right),\; \forall V \in \operatorname{Submodule}\left(K, F\right),\; \operatorname{rectangle}\left(U, V\right) = \operatorname{Submodule}.\operatorname{map}_{2}\left(\operatorname{TensorProduct}.\operatorname{mk}\left(K, E, F\right), U, V\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.rectangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rectangular tensor subspace is the image of the two subspaces under the canonical bilinear tensor map.

**Definition 1.2 (Blockmap).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] \forall F \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(F\right)] [\operatorname{Module}\left(K, F\right)] \forall g \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{TensorProduct}\left(K, E, D\right), F\right),\; \forall U \in \operatorname{Submodule}\left(K, E\right),\; \operatorname{blockMap}\left(g, U\right) = \operatorname{LinearMap}.\operatorname{flip}\left(\operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{TensorProduct}.\operatorname{curry}\left(g\right), \operatorname{Submodule}.\operatorname{subtype}\left(U\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.blockMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Currying the tensor map, restricting its left argument and flipping the two arguments gives the indicated linear map.

**Definition 1.3 (Nondirecttuples).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] [\operatorname{Fintype}\left(D\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall k \in I \to \mathbb{N},\; \operatorname{nondirectTuples}\left(k\right) = \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} v:(\forall (i:I), \operatorname{Fin}\left(k\left(i\right)\right) \to D) \mapsto (\forall i \in I,\; \operatorname{LinearIndependent}\left(K, v\left(i\right)\right)) \land (\neg (\operatorname{LinearIndependent}\left(K, (\operatorname{fun} j:\Sigma_{i:I} \operatorname{Fin}\left(k\left(i\right)\right) \mapsto v\left(\operatorname{fst}\left(j\right), \operatorname{snd}\left(j\right)\right))\right)))), \operatorname{Finset}.\operatorname{univ}\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.nondirectTuples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each block is an independent frame, while their joint family is linearly dependent.

**Theorem 1.4 (Nondirect tensor weight sum).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] [\operatorname{FiniteDimensional}\left(K, D\right)] [\operatorname{Fintype}\left(D\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall U \in I \to \operatorname{Submodule}\left(K, E\right),\; \forall r \in \mathbb{N},\; \forall m \in \mathbb{N},\; (\forall i \in I,\; \operatorname{Module}.\operatorname{finrank}\left(K, U\left(i\right)\right) = r) \Rightarrow ((\operatorname{Function}.\operatorname{Injective}\left(U\right)) \Rightarrow ((\operatorname{Module}.\operatorname{finrank}\left(K, D\right) = r \cdot m) \Rightarrow (\forall k \in I \to \mathbb{N},\; \sum_{v\in \operatorname{nondirectTuples}\left(k\right)} \left((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{(m \cdot \operatorname{Module}.\operatorname{finrank}\left(K, \operatorname{Finset}.\operatorname{sup}\left(\operatorname{Finset}.\operatorname{univ}, (\operatorname{fun} i:I \mapsto \operatorname{rectangle}\left(U\left(i\right), \operatorname{Submodule}.\operatorname{span}\left(K, \operatorname{Set}.\operatorname{range}\left(v\left(i\right)\right)\right)\right))\right)\right))}\right)^{-1} \le (\sum_{s\in \operatorname{Finset}.\operatorname{range}\left(\sum_{i\in I} k\left(i\right)\right)} (\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{(s \cdot \sum_{i\in I} k\left(i\right))}) \cdot \left((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{m}\right)^{-1})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.nondirect_tensor_weight_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed distinct left subspaces of equal dimension, the total weight of dependent tuples is bounded by an explicit finite sum times the inverse of the field cardinality to the column count.

**Definition 1.5 (Frametuples).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] [\operatorname{Fintype}\left(D\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall k \in I \to \mathbb{N},\; \operatorname{frameTuples}\left(k\right) = \operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} v:(\forall (i:I), \operatorname{Fin}\left(k\left(i\right)\right) \to D) \mapsto \forall i \in I,\; \operatorname{LinearIndependent}\left(K, v\left(i\right)\right)), \operatorname{Finset}.\operatorname{univ}\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.frameTuples` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set contains the tuples for which each individual block is an independent frame.

**Theorem 1.6 (Frame weight decomposition).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] [\operatorname{FiniteDimensional}\left(K, D\right)] [\operatorname{Fintype}\left(D\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall U \in I \to \operatorname{Submodule}\left(K, E\right),\; \forall r \in \mathbb{N},\; \forall m \in \mathbb{N},\; (\forall i \in I,\; \operatorname{Module}.\operatorname{finrank}\left(K, U\left(i\right)\right) = r) \Rightarrow ((\operatorname{Module}.\operatorname{finrank}\left(K, D\right) = r \cdot m) \Rightarrow (\forall k \in I \to \mathbb{N},\; \sum_{v\in \operatorname{frameTuples}\left(k\right)} \left((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{(m \cdot \operatorname{Module}.\operatorname{finrank}\left(K, \operatorname{Finset}.\operatorname{sup}\left(\operatorname{Finset}.\operatorname{univ}, (\operatorname{fun} i:I \mapsto \operatorname{rectangle}\left(U\left(i\right), \operatorname{Submodule}.\operatorname{span}\left(K, \operatorname{Set}.\operatorname{range}\left(v\left(i\right)\right)\right)\right))\right)\right))}\right)^{-1} = \frac{(\operatorname{Nat}.\operatorname{card}\left(\{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), (\Sigma_{i:I} \operatorname{Fin}\left(k\left(i\right)\right)) \to K, D\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\}\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), (\Sigma_{i:I} \operatorname{Fin}\left(k\left(i\right)\right)) \to K, D\right)\right):\mathbb{R})} + \sum_{v\in \operatorname{nondirectTuples}\left(k\right)} \left((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{(m \cdot \operatorname{Module}.\operatorname{finrank}\left(K, \operatorname{Finset}.\operatorname{sup}\left(\operatorname{Finset}.\operatorname{univ}, (\operatorname{fun} i:I \mapsto \operatorname{rectangle}\left(U\left(i\right), \operatorname{Submodule}.\operatorname{span}\left(K, \operatorname{Set}.\operatorname{range}\left(v\left(i\right)\right)\right)\right))\right)\right))}\right)^{-1}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.frame_weight_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weight of all blockwise independent frames separates into the contribution of joint injections and the contribution of dependent tuples.

**Theorem 1.7 (Frame incidence average).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] [\operatorname{FiniteDimensional}\left(K, D\right)] [\operatorname{Fintype}\left(D\right)] \forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall m \in \mathbb{N},\; [\operatorname{Fintype}\left(\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{TensorProduct}\left(K, E, D\right), \operatorname{Fin}\left(m\right) \to K\right)\right)] \forall U \in I \to \operatorname{Submodule}\left(K, E\right),\; \forall k \in I \to \mathbb{N},\; \frac{\sum_{g\in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{TensorProduct}\left(K, E, D\right), \operatorname{Fin}\left(m\right) \to K\right)} \sum_{v\in \operatorname{frameTuples}\left(k\right)} (\operatorname{if} \forall i \in I,\; \forall j \in \operatorname{Fin}\left(k\left(i\right)\right),\; \operatorname{blockMap}\left(g, U\left(i\right)\right)\left(v\left(i, j\right)\right) = 0 \operatorname{then} 1 \operatorname{else} 0)}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{TensorProduct}\left(K, E, D\right), \operatorname{Fin}\left(m\right) \to K\right)\right):\mathbb{R})} = \sum_{v\in \operatorname{frameTuples}\left(k\right)} \left((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{(m \cdot \operatorname{Module}.\operatorname{finrank}\left(K, \operatorname{Finset}.\operatorname{sup}\left(\operatorname{Finset}.\operatorname{univ}, (\operatorname{fun} i:I \mapsto \operatorname{rectangle}\left(U\left(i\right), \operatorname{Submodule}.\operatorname{span}\left(K, \operatorname{Set}.\operatorname{range}\left(v\left(i\right)\right)\right)\right))\right)\right))}\right)^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.frame_incidence_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counting maps and frames in either order identifies the average incidence with the sum of the inverse powers determined by the tensor spans.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.blockMap`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.frameTuples`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.frame_incidence_average`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.frame_weight_decomposition`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.nondirectTuples`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.nondirect_tensor_weight_sum`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor.rectangle`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling](MRDDensityColumnSampling.md)
