# The invariant-measure conjecture fails in three generators

## Abstract

The coefficient Jacobian of the Grassmann map S in three generators differs from the conjectured density ratio.

The exterior algebra ExteriorAlgebra Real (Fin 3 → Real) represents the Grassmann algebra on three generators. Its monomials are indexed by Finset (Fin 3), and the empty set indexes the scalar coefficient. A coefficient vector is a function Finset (Fin 3) → Real. The full coordinate space consists of functions (Finset (Fin 3) × Fin 4) → Real. For an even monomial, slots 0, 1, 2, 3 hold the coefficients of x₁, x₂, y₁, y₂; for an odd monomial they hold the coefficients of χ₁, χ₂, ψ₁, ψ₂. Parity is the cardinality of the monomial index modulo two, and scalar multiplication is the real module action.

**Definition 1.1 (The exterior monomial basis).**

$$(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.monomialBasis}: \operatorname{Module.Basis}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right), \mathbb{R}, \operatorname{ExteriorAlgebra}\left(\mathbb{R}, \operatorname{Fin}\left(3\right) \to \mathbb{R}\right)\right)) = \operatorname{Module.Basis.ExteriorAlgebra}\left(\operatorname{Pi.basisFun}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.monomialBasis` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

The standard basis of Fin 3 → Real induces the monomial basis of the exterior algebra. A finite subset specifies the ordered product of its generators, including the empty product 1.

**Definition 1.2 (The coefficient equivalence).**

$$(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.coord}: \operatorname{LinearEquiv}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{ExteriorAlgebra}\left(\mathbb{R}, \operatorname{Fin}\left(3\right) \to \mathbb{R}\right), (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})\right)) = \operatorname{Module.Basis.equivFun}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.monomialBasis}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.coord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

Module.Basis.equivFun gives the real linear equivalence from exterior elements to their monomial coefficients.

**Definition 1.3 (The coordinates of the unit).**

$$(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.unitC}: (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})) = \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.coord}\left((1: \operatorname{ExteriorAlgebra}\left(\mathbb{R}, \operatorname{Fin}\left(3\right) \to \mathbb{R}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.unitC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

The algebraic unit has scalar coefficient 1 and every nonempty monomial coefficient 0.

**Definition 1.4 (The exterior product in coordinates).**

$$\forall (u: (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})), (\forall (v: (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(u, v\right): (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})) = \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.coord}\left((\operatorname{LinearEquiv.symm}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.coord}, u\right)) \cdot (\operatorname{LinearEquiv.symm}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.coord}, v\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.gmul` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

Section 2.1 specifies the Grassmann product by anticommutation of the generators. The displayed product decodes two coefficient vectors, multiplies in ExteriorAlgebra, and takes coordinates again.

**Definition 1.5 (The inverse of an even element).**

$$\forall (u: (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ginv}\left(u\right): (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})) = (((u\left(\emptyset\right))^{-1}) \cdot (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.unitC})) - ((((u\left(\emptyset\right))^{-1})^{2}) \cdot ((u) - ((u\left(\emptyset\right)) \cdot (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.unitC})))))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.ginv` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

For an even element with nonzero scalar coefficient c, the positive-degree part has square zero in three generators. Its two-sided inverse is c⁻¹ times the unit minus c⁻² times that positive-degree part. The displayed definition is a total function on coefficient vectors; the inverse interpretation requires even parity and c ≠ 0.

**Definition 1.6 (Selecting a parity and a slot).**

$$\forall (p: \mathbb{N}), (\forall (j: \operatorname{Fin}\left(4\right)), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(p, j\right): \operatorname{ContinuousLinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R}), (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})\right)) = \operatorname{ContinuousLinearMap.pi}\left(\lambda (s: \operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right)) \mapsto (\operatorname{ite}\left((\operatorname{Finset.card}\left(s\right) \bmod 2 = p), \operatorname{ContinuousLinearMap.proj}\left((s, j)\right), (0: \operatorname{ContinuousLinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R}), \mathbb{R}\right))\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.pick` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

The continuous real linear map selects slot j on monomials of parity p and sets all other coefficients to zero. Here p is any natural number, so p outside {0,1} gives the zero map.

**Definition 1.7 (Packing the two parities).**

$$\forall (e: (\operatorname{Fin}\left(4\right) \to (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R}))), (\forall (o: (\operatorname{Fin}\left(4\right) \to (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R}))), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pack}\left(e, o\right): ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})) = \lambda (i: (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right))) \mapsto (\operatorname{ite}\left((\operatorname{Finset.card}\left(\operatorname{Prod.fst}\left(i\right)\right) \bmod 2 = 0), e\left(\operatorname{Prod.snd}\left(i\right), \operatorname{Prod.fst}\left(i\right)\right), o\left(\operatorname{Prod.snd}\left(i\right), \operatorname{Prod.fst}\left(i\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.pack` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

For each monomial and slot, the packed vector reads the corresponding even or odd coefficient according to monomial parity.

**Definition 1.8 (The even quotient y₁ over x₁).**

$$\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ratio}\left(z\right): (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R})) = \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 2, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ginv}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 0, z\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.ratio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

This coefficient vector is the product of y₁ with the explicit inverse of x₁.

**Definition 1.9 (The four even components of equation (18)).**

$$\forall (a: \mathbb{R}), (\forall (b: \mathbb{R}), (\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.evenOut}\left(a, b, z\right): (\operatorname{Fin}\left(4\right) \to (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R}))) = ![(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 2, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 2, z\right)\right), (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.unitC}) + (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 0, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 3, z\right)\right))\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ginv}\left((b) \cdot (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 0, z\right))\right)\right)) + (((b)^{-1}) \cdot (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 2, z\right), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 3, z\right)) - ((a) \cdot (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.unitC}))) - (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 2, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 3, z\right)\right))\right))), (b) \cdot (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ginv}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 2, z\right)\right)), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 0, z\right), ((((a) \cdot (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.unitC})) + (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 0, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(0, 1, z\right)\right))) - (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ratio}\left(z\right))) + (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 0, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 1, z\right)\right))])))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.evenOut` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

The four entries are u₁, u₂, v₁, v₂, in that order. They reproduce the even equations of the source's S map, with real parameters a and b acting by scalar multiplication. Each nested product follows the order of the factors in equation (18).

**Definition 1.10 (The four odd components of equation (18)).**

$$\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.oddOut}\left(z\right): (\operatorname{Fin}\left(4\right) \to (\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \to \mathbb{R}))) = ![(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 2, z\right)) - (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ratio}\left(z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 0, z\right)\right)), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 3, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 0, z\right), (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 1, z\right)) + (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.gmul}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.ratio}\left(z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pick}\left(1, 3, z\right)\right))])$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.oddOut` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

The four entries are ξ₁, ξ₂, η₁, η₂, in that order: ψ₁ − (y₁/x₁)χ₁, ψ₂, χ₁, and χ₂ + (y₁/x₁)ψ₂.

**Definition 1.11 (The full coefficient map).**

$$\forall (a: \mathbb{R}), (\forall (b: \mathbb{R}), (\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.F}\left(a, b, z\right): ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})) = \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.pack}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.evenOut}\left(a, b, z\right), \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.oddOut}\left(z\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.F` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

Equation (18) is evaluated in monomial coefficients. Quotients by even elements with nonzero scalar coefficient are products with their two-sided inverse. The output coordinates use the same (monomial, slot) layout as the inputs, with even slots u₁, u₂, v₁, v₂ and odd slots ξ₁, ξ₂, η₁, η₂.

**Definition 1.12 (Nonzero scalar denominators).**

$$\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.domain}\left(z\right)) \Leftrightarrow ((z\left((\emptyset, 0)\right) \ne 0) \land (z\left((\emptyset, 2)\right) \ne 0)))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.domain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

The scalar coefficients of x₁ and y₁ are nonzero. At b = 2 these are exactly the nonzero scalar denominators needed by equation (18).

**Definition 1.13 (The proposed density in three generators).**

$$\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.m}\left(z\right): \mathbb{R}) = ((z\left((\emptyset, 2)\right))^{3})^{-1})$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.m` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

The conjecture in Section 5 proposes the inverse cube of the scalar coefficient of y₁ for the S map in three generators.

**Definition 1.14 (The coefficient Jacobian determinant).**

$$\forall (a: \mathbb{R}), (\forall (b: \mathbb{R}), (\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.jacobian}\left(a, b, z\right): \mathbb{R}) = \operatorname{LinearMap.det}\left(\operatorname{ContinuousLinearMap.toLinearMap}\left(\operatorname{fderiv}\left(\mathbb{R}, \operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.F}\left(a, b\right), z\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.jacobian` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

Section 4 defines J as the ordinary Jacobian determinant of the map on commuting coefficients. Here fderiv is the real Fréchet derivative and LinearMap.det takes its determinant.

**Definition 1.15 (The conjectured density identity).**

$$(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.claim}) \Leftrightarrow (\forall (z: ((\operatorname{Finset}\left(\operatorname{Fin}\left(3\right)\right) \times \operatorname{Fin}\left(4\right)) \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.domain}\left(z\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.jacobian}\left(1, 2, z\right) = \frac{\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.m}\left(z\right)}{\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.m}\left(\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.F}\left(1, 2, z\right)\right)})))$$

*Formalization.* `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.claim` (`✓ std3`).

*Citation.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

At a = 1 and b = 2, the S clause of the Section 5 conjecture would give the Section 4 identity J(z) = m(z)/m(S(z)) at every point with nonzero scalar denominators.

**Theorem 1.16 (A scalar counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Algebra.GrassmannEntwiningMeasureRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/adamopoulou-papamikos-2025-grassmann-measure-refutation` (refuted) by `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"adamopoulou-papamikos-2025-grassmann-measure-refutation","declaration_gid":"D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Adamopoulou, G. Papamikos (2025). *Entwining Yang–Baxter maps over Grassmann algebras*. DOI: [10.1016/j.physd.2024.134469](https://doi.org/10.1016/j.physd.2024.134469). URL: <https://arxiv.org/abs/2311.18673v1>.

*Commentary.*

Take a = 1, b = 2, and scalar coefficients (x₁, x₂, y₁, y₂) = (1,3,2,4), with all other coefficients zero. Both scalar denominators are nonzero. The derivative preserves each monomial index and is block diagonal. Each of the four even monomials has a four-by-four block of determinant 1/2, and each of the four odd monomials has a block of determinant 1.

Thus the coefficient Jacobian is J = (1/2)⁴ = 1/16. The scalar coefficient of the output v₁ is 1, so the density ratio is m(z)/m(S(z)) = 1/8. These unequal values refute the stated identity.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.F`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.coord`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.domain`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.evenOut`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.ginv`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.gmul`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.jacobian`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.m`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.monomialBasis`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.oddOut`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.pack`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.pick`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.ratio`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.result`
- Truth anchor: `D5/S3/Quantum/Algebra/GrassmannEntwiningMeasureRefutation.unitC`
