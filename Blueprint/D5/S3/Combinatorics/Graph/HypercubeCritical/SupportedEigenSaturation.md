# Saturation of supported Huang eigenvectors

## Abstract

A supported Huang eigenvector saturates each selected edge; its nonzero coordinates have full induced degree and admit a switching function.

Let n and d be arbitrary natural numbers, U a finite subset of Q n, and z : Q n → Real. The hypotheses bound every degree of the actual induced graph on U by d, require z to vanish outside U, and give the ambient equation A z = d z. The zero vector and empty U are allowed. A is the original huangMatrix from HypercubeSubQuorum, reused through BalancedCriticalSpectrum: TRUE selects the first recursive block, so its directional signs use earlier FALSE coordinates.

The proof sums the nonnegative squared residuals (z(x) − A(x,y) z(y))² over actual edges with both endpoints in U. The existing matrix_support identifies the unit edge coefficients and zero nonedge coefficients. The support hypothesis restricts the ambient equation to selected rows; expansion and exchange of the finite sums express the energy as twice the degree-weighted squared norm minus twice d times the squared norm. The actual degree bound makes this at most zero, so each edge residual vanishes.

**Definition 1.1 (The actual nonzero selected coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.nonzeroSupport`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.nonzeroSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nonzeroSupport U z is U filtered by z(x) ≠ 0. Its membership lemma provides both selection and nonvanishing. This set may be empty and may meet several connected components; nonzeroSupport_isBalanced supplies its switching function.

**Theorem 1.2 (Every selected edge attains exact signed equality).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.edge_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.edge_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the degree, support and ambient eigen-equation hypotheses, x and y in U joined by an actual cube edge satisfy z(x) = A(x,y) z(y). This is the pointwise consequence of the vanishing squared energy. The live zero_of_adj_zero helper propagates a zero across such an edge, with both endpoints required to belong to U. The degree and balance results below consume the same signed equality.

**Theorem 1.3 (A nonzero selected coordinate has degree d).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.degree_eq_of_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.degree_eq_of_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the same three hypotheses, x in U and z(x) ≠ 0 imply that x has degree exactly d in the actual induced graph on U. Substituting edge_identity into the selected row turns that row into degree(x) times z(x); cancellation of the nonzero coordinate gives the claimed natural degree. There is no relation assumed between n and d.

**Theorem 1.4 (The nonzero support is switching-balanced).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.nonzeroSupport_isBalanced`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.nonzeroSupport_isBalanced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degree bound, vanishing outside U and ambient eigen-equation give BalancedCriticalSpectrum.IsBalanced (nonzeroSupport U z). The witness is 1 where z(x) is positive and −1 otherwise. On the nonzero support, edge_identity and the original unit Huang coefficients show that each edge coefficient equals the product of the endpoint signs. Connectedness and nonemptiness are not hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.degree_eq_of_ne_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.edge_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.nonzeroSupport`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation.nonzeroSupport_isBalanced`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](BalancedCriticalSpectrum.md)
