# CycleGeodesicProduct

## Abstract

The literal cycle-geodesic permanent admits an exact product over the roots.

**Definition 1.1 (gamma).**

$$\forall n \in \mathbb{N},\; \forall t \in \mathbb{R},\; \forall j \in \operatorname{Fin}\left(n\right),\; \forall l \in \operatorname{Fin}\left(n\right),\; \operatorname{gamma}\left(n, t, j, l\right) = \frac{\operatorname{Complex.exp}\left((2 \cdot \operatorname{Real.pi} \cdot t:\mathbb{C}) \cdot \operatorname{Complex.I}\right) - 1}{(n:\mathbb{C}) \cdot \left(\operatorname{Complex.exp}\left((\frac{2 \cdot \operatorname{Real.pi} \cdot \left((\operatorname{val}\left(l\right):\mathbb{R}) - (\operatorname{val}\left(j\right):\mathbb{R}) + t\right)}{(n:\mathbb{R})}:\mathbb{C}) \cdot \operatorname{Complex.I}\right) - 1\right)}$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.gamma` (`✓ std3`).

*Citation.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Page 7, Section 4.1: "The geodesic γ(t) is therefore a circulant matrix with explicit entries". The displayed expression is Eq. (circulant). The indices belong to Fin n and are cast before subtraction.

**Definition 1.2 (productValue).**

$$\forall n \in \mathbb{N},\; \forall z \in \mathbb{C},\; \operatorname{productValue}\left(n, z\right) = \left((n:\mathbb{C})^{-1}\right)^{n} \cdot (\prod_{k:\operatorname{Fin}\left(n\right)} ((n:\mathbb{C}) - (\operatorname{val}\left(k\right):\mathbb{C}) + (\operatorname{val}\left(k\right):\mathbb{C}) \cdot z))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.productValue` (`✓ std3`).

*Citation.* Guo-Niu Han (2000). *Généralisation de l'identité de Scott sur les permanents*. DOI: [10.1016/S0024-3795(00)00035-5](https://doi.org/10.1016/S0024-3795(00)00035-5). URL: <https://doi.org/10.1016/S0024-3795(00)00035-5>.

*Commentary.*

The polynomial product packages the exact finite-dimensional permanent value.

**Definition 1.3 (ProductFormula).**

$$ProductFormula \Leftrightarrow \left(\forall n \in \mathbb{N},\; \forall t \in \mathbb{R},\; 1 \le n \Rightarrow \left(0 < t \Rightarrow \left(t < 1 \Rightarrow \operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, t\right)\right) = \operatorname{productValue}\left(n, \operatorname{Complex.exp}\left((2 \cdot \operatorname{Real.pi} \cdot t:\mathbb{C}) \cdot \operatorname{Complex.I}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.ProductFormula` (`✓ std3`).

*Citation.* Guo-Niu Han (2000). *Généralisation de l'identité de Scott sur les permanents*. DOI: [10.1016/S0024-3795(00)00035-5](https://doi.org/10.1016/S0024-3795(00)00035-5). URL: <https://doi.org/10.1016/S0024-3795(00)00035-5>.

*Commentary.*

The product identity is stated for every positive dimension and every interior parameter.

**Theorem 1.4 (q_midpoint).**

$$\operatorname{Complex.exp}\left((2 \cdot \operatorname{Real.pi} \cdot \frac{1}{2}:\mathbb{C}) \cdot \operatorname{Complex.I}\right) = -1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.q_midpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The midpoint exponential is minus one.

**Theorem 1.5 (product_formula).**

$$\forall n \in \mathbb{N},\; \forall t \in \mathbb{R},\; 1 \le n \Rightarrow \left(0 < t \Rightarrow \left(t < 1 \Rightarrow \operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, t\right)\right) = \operatorname{productValue}\left(n, \operatorname{Complex.exp}\left((2 \cdot \operatorname{Real.pi} \cdot t:\mathbb{C}) \cdot \operatorname{Complex.I}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.product_formula` (`✓ std3`). ∎

*Citation.* Guo-Niu Han (2000). *Généralisation de l'identité de Scott sur les permanents*. DOI: [10.1016/S0024-3795(00)00035-5](https://doi.org/10.1016/S0024-3795(00)00035-5). URL: <https://doi.org/10.1016/S0024-3795(00)00035-5>.

*Commentary.*

Han's generalized Scott identity supplies this finite product in the literature. Here the Cauchy permanent is expressed as a Gaudin determinant, whose weighted Vandermonde action is a cyclic permutation times a diagonal matrix.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.ProductFormula`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.gamma`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.productValue`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.product_formula`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct.q_midpoint`
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/GaudinPermanent](GaudinPermanent.md)
