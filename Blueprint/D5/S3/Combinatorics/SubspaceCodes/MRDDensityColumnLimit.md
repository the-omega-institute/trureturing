# The column limit of MRD density

## Abstract

The fixed-field column limit of maximum rank distance code density.

**Definition 1.1 (The fixed-field column-limit assertion).**

$$claim = (\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (2 \le n) \Rightarrow ((1 \le d) \Rightarrow ((d \le n) \Rightarrow (\operatorname{Tendsto}\left((\operatorname{fun} m:\mathbb{N} \mapsto \operatorname{density}\left(K, n, m, \operatorname{mrdDimension}\left(n, m, d\right), d\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((\operatorname{if} d = 1 \operatorname{then} 1 \operatorname{else} \operatorname{P}\left(\operatorname{Fintype}.\operatorname{card}\left(K\right)\right)^{\operatorname{gaussian}\left(\operatorname{Fintype}.\operatorname{card}\left(K\right), n, (d - 1)\right)})\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit.claim` (`✓ std3`).

*Citation.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Page 1082: “Problem 2.6. Compute or estimate \delta_q^{\mathrm{rk}}(n \times m, k, d). In particular, compute its asymptotic behavior as q \rightarrow +\infty. Compute or estimate the asymptotic density of MRD codes, i.e., \delta_q^{\mathrm{rk}}(n \times m, m(n-d+1),d), as q \rightarrow +\infty and as m \rightarrow +\infty.” The field is a finite carrier K, q is Fintype.card K, n is the row count and m is the column count. The distance d satisfies 1 ≤ d ≤ n and n ≥ 2. The density uses the cardinalities of matrix subspaces; gaussian is the finite product of q-binomial factors and P is the infinite product. The assertion answers the fixed-field column-growth part of the question and includes d = 1.

**Theorem 1.2 (The fixed-field MRD density formula).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] \forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; (2 \le n) \Rightarrow ((1 \le d) \Rightarrow ((d \le n) \Rightarrow (\operatorname{Tendsto}\left((\operatorname{fun} m:\mathbb{N} \mapsto \operatorname{density}\left(K, n, m, \operatorname{mrdDimension}\left(n, m, d\right), d\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left((\operatorname{if} d = 1 \operatorname{then} 1 \operatorname{else} \operatorname{P}\left(\operatorname{Fintype}.\operatorname{card}\left(K\right)\right)^{\operatorname{gaussian}\left(\operatorname{Fintype}.\operatorname{card}\left(K\right), n, (d - 1)\right)})\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anina Gruica; Alberto Ravagnani; John Sheekey; Ferdinando Zullo (2023). *Rank-Metric Codes, Semifields, and the Average Critical Problem*. DOI: [10.1137/22M1486893](https://doi.org/10.1137/22M1486893). URL: <https://arxiv.org/abs/2201.07193v1>.

*Commentary.*

Uniform sampling of image subspaces reduces the density to injectivity of a finite family of tensor restrictions. For distinct equal-dimensional left subspaces, every dependent tuple of frames has a strict tensor dimension surplus. Its contribution vanishes as the columns grow. Mixed Gaussian moments and finite multivariate Möbius truncation give the joint zero-kernel probability. Conditioning on injectivity then gives the density limit. When d = 1 the density equals one.

## References

- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit.claim`
- Truth anchor: `D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnLimit.result`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuDefs](../CylindricPartition/LiUncuDefs.md)
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian](../CylindricPartition/LiUncuGaussian.md)
- Dependency: [D5/S3/Combinatorics/Probability/AyyerMisraHalfDensityMode](../Probability/AyyerMisraHalfDensityMode.md)
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction](MRDDensityColumnReduction.md)
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling](MRDDensityColumnSampling.md)
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor](MRDDensityColumnTensor.md)
