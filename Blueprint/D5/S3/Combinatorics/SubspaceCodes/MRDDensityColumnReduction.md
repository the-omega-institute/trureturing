# MRD density: Reduction

## Abstract

Fixed-field MRD density: reduction argument.

**Definition 1.1 (Gaussian).**

$$\forall q \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{gaussian}\left(q, a, b\right) = \prod_{h\in \operatorname{Finset}.\operatorname{range}\left(b\right)} \frac{((q:\mathbb{R})^{a} - (q:\mathbb{R})^{h})}{((q:\mathbb{R})^{b} - (q:\mathbb{R})^{h})}$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.gaussian` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1082 (arXiv v1): “Throughout the paper we will extensively use the q-binomial coefficient of non-negative integers i ≥ j, defined as”. The displayed finite product is that expression; all indices are natural numbers.

**Definition 1.2 (P).**

$$\forall q \in \mathbb{N},\; \operatorname{P}\left(q\right) = \operatorname{tprod}\left((\operatorname{fun} j:\mathbb{N} \mapsto 1 - \left((q:\mathbb{R})^{-1}\right)^{(j + 1)})\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.P` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1083: “Notice that \pi is closely related to the Euler function \phi, which is defined by \phi(x)=\prod_{i=1}^\infty (1-x^i) for x \in (-1,1). Indeed, we have \pi(q)=1/\phi(1/q).” Here P(q) = φ(1/q) = 1/π(q). The index j starts at zero, so the factor uses j+1.

**Definition 1.3 (Mindistanceatleast).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall C \in \operatorname{Submodule}\left(K, \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), K\right)\right),\; \operatorname{MinDistanceAtLeast}\left(K, n, m, d, C\right) = \left(\forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), K\right),\; (M \in C) \Rightarrow ((M \ne 0) \Rightarrow (d \le \operatorname{Matrix}.\operatorname{rank}\left(M\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.MinDistanceAtLeast` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1081: “A (rank-metric) code is a non-zero \F_q-subspace \mC \le \mat. Its minimum distance is \drk(\mC)=\min\{\rk(M) \mid M \in \mC, \; M \neq 0\}.” The predicate states the lower bound on every nonzero matrix in the subspace. K is the finite field carrier and n,m are the matrix dimensions.

**Definition 1.4 (Goodcodes).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{GoodCodes}\left(K, n, m, k, d\right) = \{C:\operatorname{Submodule}\left(K, \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), K\right)\right) // (\operatorname{Module}.\operatorname{finrank}\left(K, C\right) = k) \land (\operatorname{MinDistanceAtLeast}\left(K, n, m, d, C\right))\}$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.GoodCodes` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1082, Notation 2.5: “This number measures the proportion of rank-metric codes with minimum distance at least d within the k-dimensional ones.” The numerator consists of the k-dimensional matrix subspaces satisfying the minimum-distance predicate.

**Definition 1.5 (Allcodes).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{AllCodes}\left(K, n, m, k\right) = \{C:\operatorname{Submodule}\left(K, \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), K\right)\right) // \operatorname{Module}.\operatorname{finrank}\left(K, C\right) = k\}$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.AllCodes` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1082, Notation 2.5: “This number measures the proportion of rank-metric codes with minimum distance at least d within the k-dimensional ones.” The denominator consists of all k-dimensional matrix subspaces.

**Definition 1.6 (Density).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{density}\left(K, n, m, k, d\right) = \frac{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{GoodCodes}\left(K, n, m, k, d\right)\right):\mathbb{R})}{(\operatorname{Nat}.\operatorname{card}\left(\operatorname{AllCodes}\left(K, n, m, k\right)\right):\mathbb{R})}$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.density` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1082, Notation 2.5: “This number measures the proportion of rank-metric codes with minimum distance at least d within the k-dimensional ones.” The displayed quotient uses the cardinality of those two collections, the source numerator and its Gaussian-binomial denominator.

**Definition 1.7 (Mrddimension).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{mrdDimension}\left(n, m, d\right) = m \cdot (n - d + 1)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mrdDimension` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1082: “Note that, by definition, the density function of MRD codes is given by” δʳᵏq(n×m,m(n−d+1),d). The dimension is m(n−d+1), with natural subtraction used under d ≤ n.

**Theorem 1.8 (Limit one).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} m:\mathbb{N} \mapsto \operatorname{density}\left(K, n, m, \operatorname{mrdDimension}\left(n, m, 1\right), 1\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.limit_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full-dimensional code is unique, and every nonzero matrix has rank at least one. Thus the density for distance one is one and has the indicated limit.

**Theorem 1.9 (Product limit).**

$$\forall q \in \mathbb{N},\; (2 \le q) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} k:\mathbb{N} \mapsto \prod_{j\in \operatorname{Finset}.\operatorname{range}\left(k\right)} (1 - \left((q:\mathbb{R})^{-1}\right)^{(j + 1)})), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\operatorname{P}\left(q\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.product_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite products converge to the infinite product for every integer q at least two.

**Theorem 1.10 (Subspace of dimension le).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall E \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(K, E\right)] [\operatorname{FiniteDimensional}\left(K, E\right)] \forall W \in \operatorname{Submodule}\left(K, E\right),\; \forall r \in \mathbb{N},\; (r \le \operatorname{Module}.\operatorname{finrank}\left(K, W\right)) \Rightarrow (\exists U \in \operatorname{Submodule}\left(K, E\right),\; (\operatorname{Module}.\operatorname{finrank}\left(K, U\right) = r) \land (U \le W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.subspace_of_dimension_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A subspace contains a subspace of every dimension up to its own dimension.

**Definition 1.11 (Restrictrows).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall U \in \operatorname{Submodule}\left(K, \operatorname{Fin}\left(n\right) \to K\right),\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{restrictRows}\left(n, m, U, M\right) = \operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{Matrix}.\operatorname{toLin}'\left(\operatorname{Matrix}.\operatorname{transpose}\left(M\right)\right), \operatorname{Submodule}.\operatorname{subtype}\left(U\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.restrictRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map sends a matrix to the linear map of its transposed rows, restricted to the given subspace. The displayed expression specifies its value on every matrix; its linearity follows from linearity of composition.

**Theorem 1.12 (Mrd iff restrictions injective).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall D \in \operatorname{Type},\; [\operatorname{AddCommGroup}\left(D\right)] [\operatorname{Module}\left(K, D\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall d \in \mathbb{N},\; (d \le n) \Rightarrow (\forall f \in \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(K\right), D, \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(m\right), K\right)\right),\; (\operatorname{Function}.\operatorname{Injective}\left(f\right)) \Rightarrow ((\operatorname{MinDistanceAtLeast}\left(K, n, m, d, \operatorname{LinearMap}.\operatorname{range}\left(f\right)\right)) \Leftrightarrow (\forall U \in \operatorname{Submodule}\left(K, \operatorname{Fin}\left(n\right) \to K\right),\; (\operatorname{Module}.\operatorname{finrank}\left(K, U\right) = n - d + 1) \Rightarrow (\operatorname{Function}.\operatorname{Injective}\left(\operatorname{LinearMap}.\operatorname{comp}\left(\operatorname{restrictRows}\left(n, m, U\right), f\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mrd_iff_restrictions_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an injective generator, the rank-distance condition is equivalent to injectivity of all restrictions along subspaces of dimension n−d+1.

**Theorem 1.13 (Mixed mobius error).**

$$\forall I \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(I\right)] \forall s \in \operatorname{Finset}\left(I\right),\; \forall q \in \mathbb{R},\; (0 \le q) \Rightarrow (\forall t \in I \to \mathbb{N},\; \forall R \in \mathbb{N},\; \left|(\prod_{i\in s} (\sum_{k\in \operatorname{Finset}.\operatorname{range}\left(R + 1\right)} (-1)^{k} \cdot q^{\operatorname{Nat}.\operatorname{choose}\left(k, 2\right)} \cdot \operatorname{gaussValue}\left(q, t\left(i\right), k\right))) - (\prod_{i\in s} ((\operatorname{if} t\left(i\right) = 0 \operatorname{then} 1 \operatorname{else} 0)))\right| \le \prod_{i\in s} (1 + q^{\operatorname{Nat}.\operatorname{choose}\left(R + 1, 2\right)} \cdot \operatorname{gaussValue}\left(q, t\left(i\right), R + 1\right)) - 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mixed_mobius_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The error of the product of truncated Gaussian Möbius sums is controlled by the product of their nonnegative individual errors.

**Theorem 1.14 (Gaussian eq polynomial).**

$$\forall q \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (2 \le q) \Rightarrow ((b \le a) \Rightarrow (\operatorname{gaussian}\left(q, a, b\right) = \operatorname{gaussValue}\left((q:\mathbb{R}), a, b\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.gaussian_eq_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For in-range indices over a finite field cardinality at least two, the finite-product Gaussian coefficient equals evaluation of the integer Gaussian polynomial.

**Theorem 1.15 (Approximating limits).**

$$\forall p \in \mathbb{N} \to \mathbb{R},\; \forall a \in \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right),\; \forall b \in \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right),\; \forall c \in \mathbb{N} \to \mathbb{R},\; \forall e \in \mathbb{N} \to \mathbb{R},\; \forall L \in \mathbb{R},\; (\forall R \in \mathbb{N},\; \operatorname{Filter}.\operatorname{Eventually}\left((\operatorname{fun} m:\mathbb{N} \mapsto \left|p\left(m\right) - a\left(R, m\right)\right| \le b\left(R, m\right)), \operatorname{Filter}.\operatorname{atTop}\right)) \Rightarrow ((\forall R \in \mathbb{N},\; \operatorname{Filter}.\operatorname{Tendsto}\left(a\left(R\right), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(c\left(R\right)\right)\right)) \Rightarrow ((\forall R \in \mathbb{N},\; \operatorname{Filter}.\operatorname{Tendsto}\left(b\left(R\right), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(e\left(R\right)\right)\right)) \Rightarrow ((\operatorname{Filter}.\operatorname{Tendsto}\left(c, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(L\right)\right)) \Rightarrow ((\operatorname{Filter}.\operatorname{Tendsto}\left(e, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(0\right)\right)) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left(p, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(L\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.approximating_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Limits of approximants determine the limit of a sequence when the limiting error tends to zero.

**Theorem 1.16 (Vanishing nondirect).**

$$\forall q \in \mathbb{R},\; (1 < q) \Rightarrow (\forall C \in \mathbb{R},\; \forall w \in \mathbb{N} \to \mathbb{R},\; (\operatorname{Filter}.\operatorname{Eventually}\left((\operatorname{fun} m:\mathbb{N} \mapsto 0 \le w\left(m\right)), \operatorname{Filter}.\operatorname{atTop}\right)) \Rightarrow ((\operatorname{Filter}.\operatorname{Eventually}\left((\operatorname{fun} m:\mathbb{N} \mapsto w\left(m\right) \le C \cdot \left(q^{m}\right)^{-1}), \operatorname{Filter}.\operatorname{atTop}\right)) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left(w, \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(0\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.vanishing_nondirect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative sequence bounded eventually by a fixed constant times q to the negative column count tends to zero when q exceeds one.

**Definition 1.17 (Automorphismproduct).**

$$\forall q \in \mathbb{R},\; \forall k \in \mathbb{N},\; \operatorname{automorphismProduct}\left(q, k\right) = \prod_{h\in \operatorname{Finset}.\operatorname{range}\left(k\right)} (q^{k} - q^{h})$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.automorphismProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of qᵏ−qʰ over h from zero to k−1 is the cardinality of the general linear group when q is a finite field cardinality.

**Theorem 1.18 (Automorphism product lower).**

$$\forall q \in \mathbb{R},\; (2 \le q) \Rightarrow (\forall k \in \mathbb{N},\; q^{(k \cdot (k - 1))} \le \operatorname{automorphismProduct}\left(q, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.automorphism_product_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each factor of the general linear group product is at least qᵏ⁻¹ when q is at least two.

**Theorem 1.19 (Mobius tail bound).**

$$\forall q \in \mathbb{R},\; (2 \le q) \Rightarrow (\forall R \in \mathbb{N},\; (0 \le \frac{q^{\operatorname{Nat}.\operatorname{choose}\left(R + 1, 2\right)}}{\operatorname{automorphismProduct}\left(q, R + 1\right)}) \land (\frac{q^{\operatorname{Nat}.\operatorname{choose}\left(R + 1, 2\right)}}{\operatorname{automorphismProduct}\left(q, R + 1\right)} \le \left(q^{R}\right)^{-1}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mobius_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized first omitted Möbius coefficient is nonnegative and at most q to the negative truncation order.

**Theorem 1.20 (Mobius tail limit).**

$$\forall q \in \mathbb{R},\; (2 \le q) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} R:\mathbb{N} \mapsto \frac{q^{\operatorname{Nat}.\operatorname{choose}\left(R + 1, 2\right)}}{\operatorname{automorphismProduct}\left(q, R + 1\right)}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mobius_tail_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The omitted Möbius coefficient divided by the general linear group product tends to zero.

**Theorem 1.21 (Gaussian symmetry).**

$$\forall q \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (2 \le q) \Rightarrow ((k \le n) \Rightarrow (\operatorname{gaussian}\left(q, n, k\right) = \operatorname{gaussian}\left(q, n, (n - k)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.gaussian_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-product Gaussian coefficient is unchanged by replacing the subspace dimension by its codimension.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.AllCodes`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.GoodCodes`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.MinDistanceAtLeast`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.P`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.approximating_limits`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.automorphismProduct`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.automorphism_product_lower`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.density`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.gaussian`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.gaussian_eq_polynomial`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.gaussian_symmetry`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.limit_one`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mixed_mobius_error`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mobius_tail_bound`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mobius_tail_limit`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mrdDimension`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.mrd_iff_restrictions_injective`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.product_limit`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.restrictRows`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.subspace_of_dimension_le`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.vanishing_nondirect`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuDefs](../CylindricPartition/LiUncuDefs.md)
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian](../CylindricPartition/LiUncuGaussian.md)
- Dependency: [D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode](../Probability/AyyerMisraHalfDensityMode.md)
