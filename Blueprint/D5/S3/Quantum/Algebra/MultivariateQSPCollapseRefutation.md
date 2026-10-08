# A counterexample to Laneve--Wolf Conjecture 8

## Abstract

A two-step three-level quantum signal protocol returns from effective dimension three to two without a common monomial action on any subspace of dimension at least two.

**Definition 1.1 (Polynomial states on the torus).**

$$PolyState = \{ g: \operatorname{Fin}\left(3\right) \to \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right) \mid \forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; (\left\lVert a \right\rVert = 1) \Rightarrow ((\left\lVert b \right\rVert = 1) \Rightarrow (\sum_{i: \operatorname{Fin}\left(3\right)} \left\lVert \operatorname{eval}\left([a, b], g\left(i\right)\right) \right\rVert^{2} = 1)) \}$$

*Formalization.* `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.PolyState` (`✓ std3`).

*Citation.* L. Laneve, S. Wolf (2024). *On multivariate polynomials achievable with quantum signal processing*. DOI: [10.22331/q-2025-02-20-1641](https://doi.org/10.22331/q-2025-02-20-1641). URL: <https://arxiv.org/abs/2407.20823v2>.

*Commentary.*

A polynomial state is a vector of three complex polynomials in two variables. Its squared Euclidean norm is one whenever both variables have modulus one. The variables a and b are X(0) and X(1).

**Definition 1.2 (Effective dimension).**

$$\forall g \in \operatorname{Fin}\left(3\right) \to \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{effDim}\left(g\right) = \operatorname{finrank}\left(\mathbb{C}, \operatorname{span}\left(\mathbb{C}, \operatorname{range}\left((s: \operatorname{Finsupp}\left(\operatorname{Fin}\left(2\right), \mathbb{N}\right) \mapsto (i: \operatorname{Fin}\left(3\right) \mapsto \operatorname{coeff}\left(s, g\left(i\right)\right)))\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.effDim` (`✓ std3`).

*Citation.* L. Laneve, S. Wolf (2024). *On multivariate polynomials achievable with quantum signal processing*. DOI: [10.22331/q-2025-02-20-1641](https://doi.org/10.22331/q-2025-02-20-1641). URL: <https://arxiv.org/abs/2407.20823v2>.

*Commentary.*

For each exponent s, collect the coefficient of that monomial in each of the three coordinates. The effective dimension is the complex dimension of the span of all these coefficient vectors.

**Definition 1.3 (The three-level signal).**

$$\forall g \in \operatorname{Fin}\left(3\right) \to \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{signalStep}\left(g\right) = [g\left(0\right), \operatorname{X}\left(0\right) \cdot g\left(1\right), \operatorname{X}\left(1\right) \cdot g\left(2\right)]$$

*Formalization.* `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.signalStep` (`✓ std3`).

*Citation.* L. Laneve, S. Wolf (2024). *On multivariate polynomials achievable with quantum signal processing*. DOI: [10.22331/q-2025-02-20-1641](https://doi.org/10.22331/q-2025-02-20-1641). URL: <https://arxiv.org/abs/2407.20823v2>.

*Commentary.*

The signal leaves the first coordinate unchanged and multiplies the second and third by a and b, respectively. This is the polynomial action of diag(1,a,b).

**Definition 1.4 (Protocol C stages).**

$$\forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{specialUnitaryGroup}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \forall g \in \operatorname{Fin}\left(3\right) \to \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{stage}\left(A, g, 0\right) = g) \land (\forall j \in \mathbb{N},\; (\forall hj \in j < m,\; \forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{stage}\left(A, g, j + 1\right)\left(i\right) = \sum_{l: \operatorname{Fin}\left(3\right)} \operatorname{C}\left(\operatorname{val}\left(A\left(\operatorname{Finmk}\left(j, hj\right)\right)\right)\left(i, l\right)\right) \cdot \operatorname{signalStep}\left(\operatorname{stage}\left(A, g, j\right)\right)\left(l\right)) \land ((\neg (j < m)) \Rightarrow (\operatorname{stage}\left(A, g, j + 1\right) = \operatorname{stage}\left(A, g, j\right))))$$

*Formalization.* `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.stage` (`✓ std3`).

*Citation.* L. Laneve, S. Wolf (2024). *On multivariate polynomials achievable with quantum signal processing*. DOI: [10.22331/q-2025-02-20-1641](https://doi.org/10.22331/q-2025-02-20-1641). URL: <https://arxiv.org/abs/2407.20823v2>.

*Commentary.*

Stage zero is the input. For j less than m, stage j+1 applies the signal to stage j and then applies the constant special unitary processing matrix A(j). Thus the array index j denotes the paper's A_(j+1). Stages after m equal stage m. The constant-polynomial embedding is C, and val extracts the matrix from its special-unitary subtype.

**Definition 1.5 (The evaluated transfer operator).**

$$\forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{specialUnitaryGroup}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \operatorname{transfer}\left(A, a, b\right) = \operatorname{transferPrefix}\left(A, a, b, m\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.transfer` (`✓ std3`).

*Citation.* L. Laneve, S. Wolf (2024). *On multivariate polynomials achievable with quantum signal processing*. DOI: [10.22331/q-2025-02-20-1641](https://doi.org/10.22331/q-2025-02-20-1641). URL: <https://arxiv.org/abs/2407.20823v2>.

*Commentary.*

The prefix transfer starts at the identity. For j less than m its next value is A(j) diag(1,a,b) times its current value, and after m it stays constant. The transfer is the prefix at m, namely A_m diag(1,a,b) ... A_1 diag(1,a,b). Matrix.toEuclideanLin is the action of this matrix on complex Euclidean space in its standard orthonormal basis.

**Definition 1.6 (The subspace-isometry conclusion).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(m\right) \to \operatorname{specialUnitaryGroup}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right),\; \forall g \in PolyState,\; (\operatorname{effDim}\left(\operatorname{val}\left(g\right)\right) \le 2) \Rightarrow ((\operatorname{effDim}\left(\operatorname{stage}\left(A, \operatorname{val}\left(g\right), m\right)\right) \le 2) \Rightarrow ((\forall j \in \mathbb{N},\; (0 < j) \Rightarrow ((j < m) \Rightarrow (2 < \operatorname{effDim}\left(\operatorname{stage}\left(A, \operatorname{val}\left(g\right), j\right)\right)))) \Rightarrow (\exists H \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(3\right)\right)\right),\; \exists Hprime \in \operatorname{Submodule}\left(\mathbb{C}, \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(3\right)\right)\right),\; \exists U \in \operatorname{LinearIsometryEquiv}\left(\operatorname{RingHomId}\left(\mathbb{C}\right), H, Hprime\right),\; \exists k \in \mathbb{N},\; \exists h \in \mathbb{N},\; (2 \le \operatorname{finrank}\left(\mathbb{C}, H\right)) \land (\forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; (\left\lVert a \right\rVert = 1) \Rightarrow ((\left\lVert b \right\rVert = 1) \Rightarrow (\forall x \in H,\; \operatorname{Matrix.toEuclideanLin}\left(\operatorname{transfer}\left(A, a, b\right)\right)\left((\operatorname{val}\left(x\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(3\right)\right))\right) = a^{k} \cdot b^{h} \cdot (\operatorname{val}\left(U\left(x\right)\right): \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(3\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.claim` (`✓ std3`).

*Citation.* L. Laneve, S. Wolf (2024). *On multivariate polynomials achievable with quantum signal processing*. DOI: [10.22331/q-2025-02-20-1641](https://doi.org/10.22331/q-2025-02-20-1641). URL: <https://arxiv.org/abs/2407.20823v2>.

*Commentary.*

Conjecture 8 asserts this conclusion for polynomial states whose input and output have effective dimension at most two while every strictly intermediate state has effective dimension greater than two. EuclideanSpace(Complex,Fin(3)) is complex Euclidean space C^3 with its Hermitian norm: the squared norm is the sum of the squared coordinate moduli. H and Hprime are complex linear subspaces with the induced norm, and U:H to Hprime is a complex linear isometric equivalence. The exponents k and h are natural numbers. After choosing orthonormal bases, every special unitary matrix defines such an isometry. The conclusion permits arbitrary subspaces, isometries and exponents.

**Theorem 1.7 (Refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/laneve-2024-qsp-collapse-conjecture-refutation` (refuted) by `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"laneve-2024-qsp-collapse-conjecture-refutation","declaration_gid":"D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take m=2 with A_1 the cycle sending (x,y,z) to (z,x,y) and A_2 the inverse cycle. Both matrices are special unitary. The initial state is (3,4,12a)/13; its norm is one on the torus since 9+16+144=169. The next two states are (12ab,3,4a)/13 and (3a,4ab,12ab)/13. Their coefficient spans have dimensions two, three, and two, respectively.

The transfer is diag(a,ab,b), acting on complex Euclidean space with its Hermitian norm. If its action equals a^k b^h U on a subspace H, evaluation at (1,1) forces Ux=x in the ambient Euclidean space. Evaluation at (i,-1) then forces diag(i,-i,-1)x=i^k(-1)^h x for every x in H. The three diagonal entries are distinct, so projection onto the coordinate with that scalar eigenvalue is injective on H. Consequently H has dimension at most one, contradicting the required dimension of at least two. The collision of the last two output monomials therefore does not imply a common monomial action on a fixed two-dimensional subspace.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.PolyState`
- Truth anchor: `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.effDim`
- Truth anchor: `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.result`
- Truth anchor: `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.signalStep`
- Truth anchor: `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.stage`
- Truth anchor: `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.transfer`
