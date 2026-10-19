# Planar fans and polynomial approximation

## Abstract

Planar fans and rotational moment cancellation.

**Definition 1.1 (IsSimplePolygon).**

$$\forall n: \mathbb{N}, \forall v: Fin\left(((n)+(3))\right) \to \mathbb{C}, IsSimplePolygon\left(v\right) \equiv \left(((\forall i: Fin\left(((n)+(3))\right), \forall j: Fin\left(((n)+(3))\right), (i \ne j) \Rightarrow ((j \ne (i)+(1)) \Rightarrow ((i \ne (j)+(1)) \Rightarrow (Disjoint\left((segment\left(\mathbb{R}\right)\left((v\left(i\right))\right)\left((v\left(((i)+(1))\right))\right))\right)\left((segment\left(\mathbb{R}\right)\left((v\left(j\right))\right)\left((v\left(((j)+(1))\right))\right))\right)))))) \land (((\forall i: Fin\left(((n)+(3))\right), \operatorname{Set}.\operatorname{inter}\left(segment\left(\mathbb{R}\right)\left((v\left(i\right))\right)\left((v\left(((i)+(1))\right))\right), segment\left(\mathbb{R}\right)\left((v\left(((i)+(1))\right))\right)\left((v\left(((i)+(2))\right))\right)\right) = \{v\left(((i)+(1))\right)\})) \land ((\forall i: Fin\left(((n)+(3))\right), \neg (Collinear\left(\mathbb{R}\right)\left(\{v\left(i\right), v\left(((i)+(1))\right), v\left(((i)+(2))\right)\}\right)))))\right)$$

*Formalization.* `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.IsSimplePolygon` (`✓ std3`).

*Citation.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

Nonadjacent sides are disjoint, adjacent sides intersect exactly at their common endpoint, and each consecutive triple is noncollinear.

**Definition 1.2 (IsPolygonRegion).**

$$\forall n: \mathbb{N}, \forall \omega: Set\left(\mathbb{C}\right), IsPolygonRegion\left(n, \omega\right) \equiv \exists v: Fin\left(((n)+(3))\right) \to \mathbb{C}, (IsSimplePolygon\left(v\right)) \land ((IsOpen\left(\omega\right)) \land ((IsConnected\left(\omega\right)) \land ((Bornology.\operatorname{IsBounded}\left(\omega\right)) \land (frontier\left(\omega\right) = \operatorname{Polygon}.\operatorname{boundary}\left(\mathbb{R}, (\langle v\rangle: Polygon\left(\mathbb{C}, (n+3)\right))\right)))))$$

*Formalization.* `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.IsPolygonRegion` (`✓ std3`).

*Citation.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

A polygon region is open, connected and bounded, with frontier equal to Polygon.boundary of a simple polygon. The closed path is v₀ → v₁ → ⋯ → vₙ₊₂ → v₀; its n + 3 sides are the affine segments Polygon.edgeSet.

**Theorem 1.3 (Area form of two polar points).**

$$\forall A B \theta \phi: \mathbb{R}, Complex.\operatorname{orientation}.\operatorname{areaForm}\left(circleMap\left(0, A, \theta\right), circleMap\left(0, B, \phi\right)\right) = A\cdot B\cdot \operatorname{Real}.\operatorname{sin}\left((\phi-\theta)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.cross_polarPoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The oriented area of two polar vectors is the product of their radii and the sine of their angle difference.

**Definition 1.4 (Linear map prescribed on one and I).**

$$\forall a b: \mathbb{C}, triangleMap\left(a, b\right) = Complex.\operatorname{basisOneI}.\operatorname{constr}\left(\mathbb{R}, ![a, b]\right)$$

*Formalization.* `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The real linear map sends the basis vectors 1 and I to a and b.

**Theorem 1.5 (triangleMap apply).**

$$\forall a: \mathbb{C}, \forall b: \mathbb{C}, \forall z: \mathbb{C}, triangleMap\left(a\right)\left(b\right)\left(z\right) = ((z.\operatorname{re})\cdot(a))+((z.\operatorname{im})\cdot(b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes triangleMap apply.

**Theorem 1.6 (triangle mem iff cross).**

$$\forall a: \mathbb{C}, \forall b: \mathbb{C}, \forall z: \mathbb{C}, (0 < Complex.\operatorname{orientation}.\operatorname{areaForm}\left(a\right)\left(b\right)) \Rightarrow ((z \in convexHull\left(\mathbb{R}\right)\left(\{0, a, b\}\right)) \Leftrightarrow ((0 \le Complex.\operatorname{orientation}.\operatorname{areaForm}\left(z\right)\left(b\right)) \land ((0 \le Complex.\operatorname{orientation}.\operatorname{areaForm}\left(a\right)\left(z\right)) \land ((Complex.\operatorname{orientation}.\operatorname{areaForm}\left(z\right)\left(b\right))+(Complex.\operatorname{orientation}.\operatorname{areaForm}\left(a\right)\left(z\right)) \le Complex.\operatorname{orientation}.\operatorname{areaForm}\left(a\right)\left(b\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangle_mem_iff_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes triangle mem iff cross.

**Definition 1.7 (complexCap).**

$$complexCap = \operatorname{Set}.\operatorname{preimage}\left(Complex.\operatorname{measurableEquivRealProd}, (regionBetween\left((Function.\operatorname{const}\left(\mathbb{R}\right)\left(0\right))\right)\left((\operatorname{fun} x: \mathbb{R} \mapsto (1)-(x))\right)\left((Ioo\left((\frac{1}{2})\right)\left(1\right))\right))\right)$$

*Formalization.* `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.complexCap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

This open cap is the part of the reference triangle whose real coordinate exceeds one half.

**Theorem 1.8 (complexCap isOpen).**

$$IsOpen\left(complexCap\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.complexCap_isOpen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes complexCap isOpen.

**Theorem 1.9 (complexCap volume).**

$$volume\left(complexCap\right) = ENNReal.\operatorname{ofReal}\left((\frac{1}{8}: \mathbb{R})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.complexCap_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes complexCap volume.

**Theorem 1.10 (finite cyclic fan frontier).**

$$\forall t: \mathbb{N}, [NeZero\left(t\right)] \forall v: Fin\left(t\right) \to \mathbb{C}, (\forall i, 0 < Complex.\operatorname{orientation}.\operatorname{areaForm}\left((v\left(i\right))\right)\left((v\left(((i)+(1))\right))\right)) \Rightarrow (((0: \mathbb{C}) \in interior\left((\operatorname{Set}.\operatorname{iUnion}\left((\operatorname{fun} i \mapsto convexHull\left(\mathbb{R}\right)\left(\{0, v\left(i\right), v\left(((i)+(1))\right)\}\right))\right))\right)) \Rightarrow ((Pairwise\left((\operatorname{fun} i j \mapsto AEDisjoint\left(volume\right)\left((convexHull\left(\mathbb{R}\right)\left(\{0, v\left(i\right), v\left(((i)+(1))\right)\}\right))\right)\left((convexHull\left(\mathbb{R}\right)\left(\{0, v\left(j\right), v\left(((j)+(1))\right)\}\right))\right))\right)) \Rightarrow (frontier\left((interior\left((\operatorname{Set}.\operatorname{iUnion}\left((\operatorname{fun} i \mapsto convexHull\left(\mathbb{R}\right)\left(\{0, v\left(i\right), v\left(((i)+(1))\right)\}\right))\right))\right))\right) = \operatorname{Set}.\operatorname{iUnion}\left((\operatorname{fun} i \mapsto segment\left(\mathbb{R}\right)\left((v\left(i\right))\right)\left((v\left(((i)+(1))\right))\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.finite_cyclic_fan_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

For a finite cyclic fan with positive oriented triangles, disjoint triangle interiors in measure, and the origin interior to the fan, the frontier of its interior consists exactly of the outer edges.

**Theorem 1.11 (integral pow eq zero of rotation).**

$$\forall a: Circle, \forall k: \mathbb{N}, \forall \omega: Set\left(\mathbb{C}\right), (\operatorname{Set}.\operatorname{image}\left((rotation\left(a\right)), \omega\right) = \omega) \Rightarrow ((((a: \mathbb{C}))^{k} \ne 1) \Rightarrow ((\int_{z \in \omega} (z)^{k}) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.integral_pow_eq_zero_of_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes integral pow eq zero of rotation.

**Definition 1.12 (rhoN).**

$$\forall N: \mathbb{N}, \forall \omega: Set\left(\mathbb{C}\right), rhoN\left(N, \omega\right) = \operatorname{iInf}\left((\operatorname{fun} p: Polynomial.\operatorname{degreeLE}\left(\mathbb{C}\right)\left((N: WithBot\left(\mathbb{N}\right))\right) \mapsto \int_{z \in \omega} (\left\lVert ((starRingEnd\left(\mathbb{C}\right))\left(z\right))-((p: Polynomial\left(\mathbb{C}\right)).\operatorname{eval}\left(z\right)) \right\rVert)^{2})\right)$$

*Formalization.* `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.rhoN` (`✓ std3`).

*Citation.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

Section 1, p. 2: “Notice that ρ_N(Ω) is the square of the distance from z̄ to P_N in L²(Ω, dA).”. Here P_N is the space of polynomials of degree at most N. The measure in every integral is planar volume on the complex numbers.

**Theorem 1.13 (no max of unbounded family).**

$$\forall N: \mathbb{N}, \forall n: \mathbb{N}, \forall F: \mathbb{N} \to Set\left(\mathbb{C}\right), (\forall r, IsPolygonRegion\left(n\right)\left((F\left(r\right))\right)) \Rightarrow ((\forall r, volume\left((F\left(r\right))\right) = 1) \Rightarrow ((\forall C: \mathbb{R}, \exists r, C < rhoN\left(N\right)\left((F\left(r\right))\right)) \Rightarrow (\neg (\exists P: Set\left(\mathbb{C}\right), (IsPolygonRegion\left(n\right)\left(P\right)) \land ((volume\left(P\right) = 1) \land (\forall Q: Set\left(\mathbb{C}\right), (IsPolygonRegion\left(n\right)\left(Q\right)) \Rightarrow ((volume\left(Q\right) = 1) \Rightarrow (rhoN\left(N\right)\left(Q\right) \le rhoN\left(N\right)\left(P\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.no_max_of_unbounded_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes no max of unbounded family.

**Theorem 1.14 (norm sq smul add ge).**

$$\forall a: \mathbb{C}, \forall b: \mathbb{C}, \forall s: \mathbb{R}, \forall t: \mathbb{R}, (0 \le s) \Rightarrow ((0 \le t) \Rightarrow ((0 \le ((a)\cdot(conj\left(b\right))).\operatorname{re}) \Rightarrow (((s)^{2})\cdot((\left\lVert a \right\rVert)^{2}) \le (\left\lVert ((s)\cdot(a))+((t)\cdot(b)) \right\rVert)^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.norm_sq_smul_add_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes norm sq smul add ge.

**Definition 1.15 (polarVertex).**

$$\forall m: \mathbb{N}, \forall r: Fin\left(((2)\cdot(m))\right) \to \mathbb{R}, \forall i: Fin\left(((2)\cdot(m))\right), polarVertex\left(m, r, i\right) = circleMap\left(0\right)\left((r\left(i\right))\right)\left((((val\left(i\right): \mathbb{R}))\cdot((\frac{Real.\operatorname{pi}}{(m: \mathbb{R})})))\right)$$

*Formalization.* `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polarVertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The vertices have the prescribed radii at equally spaced angles π/m.

**Theorem 1.16 (polar cyclic fan pairwise aeDisjoint).**

$$\forall m: \mathbb{N}, [NeZero\left(m\right)] (3 \le m) \Rightarrow (\forall r: Fin\left(((2)\cdot(m))\right) \to \mathbb{R}, (\forall i, 0 \le r\left(i\right)) \Rightarrow (Pairwise\left((\operatorname{fun} i j: Fin\left(((2)\cdot(m))\right) \mapsto AEDisjoint\left(volume\right)\left((convexHull\left(\mathbb{R}\right)\left(\{0, polarVertex\left(m\right)\left(r\right)\left(i\right), polarVertex\left(m\right)\left(r\right)\left(((i)+(1))\right)\}\right))\right)\left((convexHull\left(\mathbb{R}\right)\left(\{0, polarVertex\left(m\right)\left(r\right)\left(j\right), polarVertex\left(m\right)\left(r\right)\left(((j)+(1))\right)\}\right))\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polar_cyclic_fan_pairwise_aeDisjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes polar cyclic fan pairwise aeDisjoint.

**Theorem 1.17 (polar cyclic nonadjacent disjoint).**

$$\forall m: \mathbb{N}, [NeZero\left(m\right)] (3 \le m) \Rightarrow (\forall r: Fin\left(((2)\cdot(m))\right) \to \mathbb{R}, (\forall i, 0 < r\left(i\right)) \Rightarrow (\forall i: Fin\left(((2)\cdot(m))\right), \forall j: Fin\left(((2)\cdot(m))\right), (i \ne j) \Rightarrow ((j \ne (i)+(1)) \Rightarrow ((i \ne (j)+(1)) \Rightarrow (Disjoint\left((segment\left(\mathbb{R}\right)\left((polarVertex\left(m\right)\left(r\right)\left(i\right))\right)\left((polarVertex\left(m\right)\left(r\right)\left(((i)+(1))\right))\right))\right)\left((segment\left(\mathbb{R}\right)\left((polarVertex\left(m\right)\left(r\right)\left(j\right))\right)\left((polarVertex\left(m\right)\left(r\right)\left(((j)+(1))\right))\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polar_cyclic_nonadjacent_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes polar cyclic nonadjacent disjoint.

**Theorem 1.18 (Consecutive polar cones cover the plane).**

$$\forall m: \mathbb{N}, [NeZero\left(m\right)] (3 \le m) \Rightarrow (\forall r: Fin\left(((2)\cdot(m))\right) \to \mathbb{R}, (\forall i, 0 < r\left(i\right)) \Rightarrow (\forall z: \mathbb{C}, \exists i: Fin\left(((2)\cdot(m))\right), (0 \le Complex.\operatorname{orientation}.\operatorname{areaForm}\left((polarVertex\left(m\right)\left(r\right)\left(i\right))\right)\left(z\right)) \land (0 \le Complex.\operatorname{orientation}.\operatorname{areaForm}\left(z\right)\left((polarVertex\left(m\right)\left(r\right)\left(((i)+(1))\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polar_fan_conic_coverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The consecutive rays of a positive radial 2m-gon cover every direction. Represent the argument in [0, 2π), divide by π/m and take its natural floor to select a sector.

**Theorem 1.19 (rhoN eq secondMoment of moments).**

$$\forall N: \mathbb{N}, \forall \omega: Set\left(\mathbb{C}\right), (Bornology.\operatorname{IsBounded}\left(\omega\right)) \Rightarrow ((\forall k: \mathbb{N}, (1 \le k) \Rightarrow ((k \le (N)+(1)) \Rightarrow ((\int_{z \in \omega} (z)^{k}) = 0))) \Rightarrow (rhoN\left(N\right)\left(\omega\right) = \int_{z \in \omega} (\left\lVert z \right\rVert)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.rhoN_eq_secondMoment_of_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes rhoN eq secondMoment of moments.

**Theorem 1.20 (secondMoment ge on subset).**

$$\forall \omega: Set\left(\mathbb{C}\right), \forall s: Set\left(\mathbb{C}\right), (Bornology.\operatorname{IsBounded}\left(\omega\right)) \Rightarrow ((MeasurableSet\left(s\right)) \Rightarrow ((s \subseteq \omega) \Rightarrow (\forall C: \mathbb{R}, (\forall z, z \in s \Rightarrow (C \le (\left\lVert z \right\rVert)^{2})) \Rightarrow ((C)\cdot((volume\left(s\right)).\operatorname{toReal}) \le \int_{z \in \omega} (\left\lVert z \right\rVert)^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.secondMoment_ge_on_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes secondMoment ge on subset.

**Theorem 1.21 (triangleMap complexCap subset hull).**

$$\forall a: \mathbb{C}, \forall b: \mathbb{C}, \operatorname{Set}.\operatorname{image}\left((triangleMap\left(a\right)\left(b\right)), complexCap\right) \subseteq convexHull\left(\mathbb{R}\right)\left(\{0, a, b\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap_complexCap_subset_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes triangleMap complexCap subset hull.

**Theorem 1.22 (triangleMap det).**

$$\forall a: \mathbb{C}, \forall b: \mathbb{C}, LinearMap.\operatorname{det}\left((triangleMap\left(a\right)\left(b\right))\right) = ((a.\operatorname{re})\cdot(b.\operatorname{im}))-((a.\operatorname{im})\cdot(b.\operatorname{re}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes triangleMap det.

**Theorem 1.23 (triangle volume).**

$$\forall a: \mathbb{C}, \forall b: \mathbb{C}, volume\left((convexHull\left(\mathbb{R}\right)\left(\{0, a, b\}\right))\right) = ENNReal.\operatorname{ofReal}\left((\frac{\left|((a.\operatorname{re})\cdot(b.\operatorname{im}))-((a.\operatorname{im})\cdot(b.\operatorname{re}))\right|}{2})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangle_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Kraus and B. Simanek (2024). *New Perspectives on Torsional Rigidity and Polynomial Approximations of z-bar*. DOI: [10.1007/s10659-024-10087-4](https://doi.org/10.1007/s10659-024-10087-4). URL: <https://arxiv.org/abs/2309.16450>.

*Commentary.*

The displayed statement describes triangle volume.

## References

- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.IsPolygonRegion`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.IsSimplePolygon`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.complexCap`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.complexCap_isOpen`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.complexCap_volume`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.cross_polarPoint`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.finite_cyclic_fan_frontier`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.integral_pow_eq_zero_of_rotation`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.no_max_of_unbounded_family`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.norm_sq_smul_add_ge`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polarVertex`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polar_cyclic_fan_pairwise_aeDisjoint`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polar_cyclic_nonadjacent_disjoint`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.polar_fan_conic_coverage`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.rhoN`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.rhoN_eq_secondMoment_of_moments`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.secondMoment_ge_on_subset`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap_apply`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap_complexCap_subset_hull`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangleMap_det`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangle_mem_iff_cross`
- Truth anchor: `D5/S3/Analytic/Torsion/PlanarFanPolynomialApproximation.triangle_volume`
- Dependency: [D5/S3/Geometry/Gluing/CyclicTriangleDisk](../../Geometry/Gluing/CyclicTriangleDisk.md)
