# MRD density: Sampling

## Abstract

Fixed-field MRD density: sampling argument.

**Definition 1.1 (Imagecode).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] \forall f \in \{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), D, E\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\},\; \operatorname{val}\left((\operatorname{imageCode}\left(f\right):\{U:\operatorname{Submodule}\left(K, E\right) // \operatorname{Module}.\operatorname{finrank}\left(K, U\right) = \operatorname{Module}.\operatorname{finrank}\left(K, D\right)\})\right) = \operatorname{LinearMap}.\operatorname{range}\left(\operatorname{val}\left(f\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.imageCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The underlying subspace is the range of the injective linear map; its dimension equals that of the source.

**Theorem 1.2 (Uniform image ratio).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] [\operatorname{FiniteDimensional}\left(K, D\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] [\operatorname{Finite}\left(K\right)] [\operatorname{Finite}\left(D\right)] [\operatorname{Finite}\left(E\right)] \forall P \in \{U:\operatorname{Submodule}\left(K, E\right) // \operatorname{Module}.\operatorname{finrank}\left(K, U\right) = \operatorname{Module}.\operatorname{finrank}\left(K, D\right)\} \to \operatorname{Prop},\; \frac{(\operatorname{Nat}.\operatorname{card}\left(\{f:\{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), D, E\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\} // P\left(\operatorname{imageCode}\left(f\right)\right)\}\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), D, E\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\}\right):\mathbb{R})} = \frac{(\operatorname{Nat}.\operatorname{card}\left(\{U:\{U:\operatorname{Submodule}\left(K, E\right) // \operatorname{Module}.\operatorname{finrank}\left(K, U\right) = \operatorname{Module}.\operatorname{finrank}\left(K, D\right)\} // P\left(U\right)\}\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\{U:\operatorname{Submodule}\left(K, E\right) // \operatorname{Module}.\operatorname{finrank}\left(K, U\right) = \operatorname{Module}.\operatorname{finrank}\left(K, D\right)\}\right):\mathbb{R})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.uniform_image_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every subspace of the source dimension has the same number of injective parametrizations. Therefore the proportion of maps whose image has a property equals the proportion of subspaces having that property.

**Definition 1.3 (Injectionframeequiv).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] \forall k \in \mathbb{N},\; (\forall f \in \{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{Fin}\left(k\right) \to K, E\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\},\; \operatorname{val}\left(\operatorname{injectionFrameEquiv}\left(k\right)\left(f\right)\right) = (\operatorname{fun} i:\operatorname{Fin}\left(k\right) \mapsto \operatorname{val}\left(f\right)\left(\operatorname{Pi}.\operatorname{basisFun}\left(K, \operatorname{Fin}\left(k\right)\right)\left(i\right)\right))) \land (\forall v \in \{v:\operatorname{Fin}\left(k\right) \to E // \operatorname{LinearIndependent}\left(K, v\right)\},\; \operatorname{val}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{injectionFrameEquiv}\left(k\right)\right)\left(v\right)\right) = \operatorname{Module}.\operatorname{Basis}.\operatorname{constr}\left(\operatorname{Pi}.\operatorname{basisFun}\left(K, \operatorname{Fin}\left(k\right)\right), K, \operatorname{val}\left(v\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.injectionFrameEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An injective linear map corresponds to its values on the standard basis. The inverse extends an independent frame linearly using that basis.

**Theorem 1.4 (Real injection count).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] \forall k \in \mathbb{N},\; (k \le \operatorname{Module}.\operatorname{finrank}\left(K, E\right)) \Rightarrow ((\operatorname{Nat}.\operatorname{card}\left(\{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{Fin}\left(k\right) \to K, E\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\}\right):\mathbb{R}) = \prod_{h\in \operatorname{Finset}.\operatorname{range}\left(k\right)} ((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{\operatorname{Module}.\operatorname{finrank}\left(K, E\right)} - (\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{h}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.real_injection_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of injective linear maps is the product of the choices of successive independent images of a basis.

**Theorem 1.5 (Subspace card real).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] \forall k \in \mathbb{N},\; (k \le \operatorname{Module}.\operatorname{finrank}\left(K, E\right)) \Rightarrow ((\operatorname{Nat}.\operatorname{card}\left(\{U:\operatorname{Submodule}\left(K, E\right) // \operatorname{Module}.\operatorname{finrank}\left(K, U\right) = k\}\right):\mathbb{R}) = \prod_{h\in \operatorname{Finset}.\operatorname{range}\left(k\right)} \frac{((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{\operatorname{Module}.\operatorname{finrank}\left(K, E\right)} - (\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{h})}{((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{k} - (\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{h})})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.subspace_card_real` (`✓ std3`). ∎

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1082 (arXiv v1): “It is well known that \qbin{i}{j}{q} counts the number of j-dimensional subspaces of an i-dimensional space over \F_q.” Dividing the number of independent frames by the number of their changes of basis gives the displayed product.

**Theorem 1.6 (Annihilating map fraction).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] \forall F \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(F\right)] [\operatorname{Module}\left(K, F\right)] [\operatorname{FiniteDimensional}\left(K, F\right)] \forall T \in \operatorname{Submodule}\left(K, E\right),\; \frac{(\operatorname{Nat}.\operatorname{card}\left(\{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), E, F\right) // T \le \operatorname{LinearMap}.\operatorname{ker}\left(f\right)\}\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), E, F\right)\right):\mathbb{R})} = \left((\operatorname{Fintype}.\operatorname{card}\left(K\right):\mathbb{R})^{(\operatorname{Module}.\operatorname{finrank}\left(K, T\right) \cdot \operatorname{Module}.\operatorname{finrank}\left(K, F\right))}\right)^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.annihilating_map_fraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Annihilating a fixed subspace removes its dimension times the codomain dimension in the exponent of the number of linear maps.

**Theorem 1.7 (Injective fraction limit).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall r \in \mathbb{N},\; \forall n \in \mathbb{N},\; (1 \le r) \Rightarrow ((r < n) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} m:\mathbb{N} \mapsto \frac{(\operatorname{Nat}.\operatorname{card}\left(\{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{Fin}\left(m \cdot r\right) \to K, \operatorname{Fin}\left(m \cdot n\right) \to K\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\}\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{Fin}\left(m \cdot r\right) \to K, \operatorname{Fin}\left(m \cdot n\right) \to K\right)\right):\mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(1\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.injective_fraction_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both dimensions grow linearly with the column count and the codomain grows faster, the fraction of injective maps tends to one.

**Theorem 1.8 (Fixed source injection limit).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall k \in \mathbb{N},\; \forall r \in \mathbb{N},\; (1 \le r) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} m:\mathbb{N} \mapsto \frac{(\operatorname{Nat}.\operatorname{card}\left(\{f:\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{Fin}\left(k\right) \to K, \operatorname{Fin}\left(m \cdot r\right) \to K\right) // \operatorname{Function}.\operatorname{Injective}\left(f\right)\}\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), \operatorname{Fin}\left(k\right) \to K, \operatorname{Fin}\left(m \cdot r\right) \to K\right)\right):\mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.fixed_source_injection_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed source dimension and a codomain of positive linearly growing dimension, the fraction of injective maps tends to one.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.annihilating_map_fraction`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.fixed_source_injection_limit`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.imageCode`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.injectionFrameEquiv`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.injective_fraction_limit`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.real_injection_count`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.subspace_card_real`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling.uniform_image_ratio`
