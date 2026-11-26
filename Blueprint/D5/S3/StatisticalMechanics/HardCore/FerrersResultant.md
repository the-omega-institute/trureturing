# Stability of Ferrers independence polynomials

## Abstract

The actual Ferrers graph is closed stable exactly when all coefficients of its pair-sum resultant are nonnegative.

**Definition 1.1 (Number of free vertices).**

$$e_{i}=(n-1-i)+(m-\lambda_{i})$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.rowExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

With zero-based i, the two differences count later rows and columns outside the selected row's neighborhood. The differences are natural subtractions.

**Definition 1.2 (Polynomial from row lengths).**

$$P\left(X\right)=(1+X)^{m}+X\sum_{i}(1+X)^{e_{i}}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.explicitPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

The first summand selects columns only. Every other summand selects its least row and any subset of the free vertices.

**Definition 1.3 (Largest available cardinality).**

$$d=\operatorname{max}\left(m, \max_{i}(e_{i}+1)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.degreeBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

Take the maximum over the column-only case and all choices of least row. The maximum of the empty row family is zero.

**Definition 1.4 (Partition criterion).**

$$\begin{aligned}p=P\land(\forall j\in\mathbb{N}, [X^{j}]p=N\left(j\right))\land N\left(0\right)=1\land\\(\forall j\in\mathbb{N}, N\left(j+1\right)=\operatorname{choose}\left(m, j+1\right)+\sum_{i}\operatorname{choose}\left(e_{i}, j\right))\land\\0< d\land\operatorname{deg}\left(p\right)=d\land0<\operatorname{lc}\left(p\right)\land\operatorname{deg}\left(r\right)=d^{2}\land\operatorname{lc}\left(r\right)=(\operatorname{lc}\left(p\right))^{2d}\land\\((\forall z\in\mathbb{C}, p\left(z\right)=0\implies\Re z\le0)\iff S)\land\\(S\implies([T^{0}]r=0\iff(\exists z\in\mathbb{C}, p\left(z\right)=0\land\Re z=0)))\land[X^{0}]p=1\\S\iff(\forall 0\le j\le d^{2}, 0\le[T^{j}]r)\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

For every positive row count n, let λ be nonincreasing with positive entries and put m = λ₀. Use G for the Ferrers graph, p for its actual independence polynomial, N(j) for the number of actual independent j-sets, P for the row-length formula, d for the maximum above, and r for the pair-sum resultant of P. The scan S tests every integer index from zero through d², inclusive.

**Theorem 1.5 (Exact answer to Question 4.1).**

$$\begin{aligned}p=P\land(\forall j\in\mathbb{N}, [X^{j}]p=N\left(j\right))\land N\left(0\right)=1\land\\(\forall j\in\mathbb{N}, N\left(j+1\right)=\operatorname{choose}\left(m, j+1\right)+\sum_{i}\operatorname{choose}\left(e_{i}, j\right))\land\\0< d\land\operatorname{deg}\left(p\right)=d\land0<\operatorname{lc}\left(p\right)\land\operatorname{deg}\left(r\right)=d^{2}\land\operatorname{lc}\left(r\right)=(\operatorname{lc}\left(p\right))^{2d}\land\\((\forall z\in\mathbb{C}, p\left(z\right)=0\implies\Re z\le0)\iff S)\land\\(S\implies([T^{0}]r=0\iff(\exists z\in\mathbb{C}, p\left(z\right)=0\land\Re z=0)))\land[X^{0}]p=1\\S\iff(\forall 0\le j\le d^{2}, 0\le[T^{j}]r)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ta Quang Anh, Do Trong Hoang and Nguyen Minh Nhat (2026). *Stability of independence polynomials of well-covered Ferrers graphs*. URL: <https://arxiv.org/abs/2611.26962v1>.

*Commentary.*

The least-row count identifies p with P and gives the coefficients. A maximal term contributes positively at degree d. A root of p in the open right half-plane would produce a positive real resultant root by conjugate pairing. When the scan passes, a zero pair sum has both real parts zero, so the constant coefficient detects the imaginary axis. The empty independent set gives p(0) equal to one.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.degreeBound`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.explicitPolynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.result`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/FerrersResultant.rowExponent`
- Dependency: [D5/S3/Analytic/Polynomial/PairSumStability](../../Analytic/Polynomial/PairSumStability.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/FerrersGraphCount](FerrersGraphCount.md)
