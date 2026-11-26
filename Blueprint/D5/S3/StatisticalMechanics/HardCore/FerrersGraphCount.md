# The Ferrers independence polynomial

## Abstract

Count independent sets of the Ferrers graph by their least selected row.

**Definition 1.1 (Disjoint vertex sets).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.Vertex`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.Vertex` (`✓ std3`).

*Citation.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

Rows and columns form the tagged disjoint sum of the two finite index sets.

**Definition 1.2 (Ferrers adjacency).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.graph`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.graph` (`✓ std3`).

*Citation.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

With zero-based row and column indices, row i meets column j exactly when j is less than the length of row i. Edges only join the two parts.

**Theorem 1.3 (Least-row enumeration).**

$$\operatorname{I}\left(G, X\right)=(1+X)^{m}+X\sum_{i}(1+X)^{e_{i}}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.independencePolynomial_ferrers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

The row lengths are nonincreasing. The sum ranges over the zero-based row indices and e_i is n − 1 − i + (m − λ_i), with natural subtraction. The first term counts column-only sets. If i is the least selected row, the later rows and the columns outside its neighborhood may be chosen freely.

**Theorem 1.4 (Coefficients count actual sets).**

$$[X^{k}]\operatorname{I}\left(G, X\right)=\Vert\operatorname{indepSetFinset}\left(G, k\right)\Vert$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.coeff_independencePolynomial_eq_card_indepSetFinset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite simple graph G, selecting the degree-k monomials keeps precisely the Mathlib independent sets of size k.

**Theorem 1.5 (The empty independent set).**

$$\Vert\operatorname{indepSetFinset}\left(G, 0\right)\Vert=1$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.card_indepSetFinset_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite simple graph G, the empty subset is the unique independent set of size zero.

**Theorem 1.6 (Independent sets of positive size).**

$$\Vert\operatorname{indepSetFinset}\left(G, k+1\right)\Vert=\operatorname{choose}\left(m, k+1\right)+\sum_{i}\operatorname{choose}\left(e_{i}, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.card_indepSetFinset_ferrers_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

The row lengths are nonincreasing. For each possible least row i, choose k additional vertices from the e_i free vertices. Column-only sets choose k + 1 columns.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.Vertex`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.card_indepSetFinset_ferrers_succ`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.card_indepSetFinset_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.coeff_independencePolynomial_eq_card_indepSetFinset`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.graph`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount.independencePolynomial_ferrers`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](IndependentPartitionDeletion.md)
