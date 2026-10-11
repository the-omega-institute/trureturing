# Two-wall universality in power-rank form

## Abstract

Every two-wall cyclicity class has maximal hypereclectic power ranks, attained generically by the eclectic operator.

Work over the complex numbers. A filling contains a letters 1, b letters 2 and two walls 3, so L = a+b+2. Cyclicity indices k range over Fin(L), with val(k) in {0,...,L−1}. The space retains literal periodic words; its cyclicity class is the eigenspace of the one-site right shift. The three coupling coordinates xi(0), xi(1), xi(2) multiply F1, F2, F3, respectively. Thus vector3(0,0,1) is the hypereclectic point with coefficient one on F3.

**Definition 1.1 (Cyclicity eigenvalue).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \operatorname{eigenvalue}\left(a, b, k\right) = \operatorname{exp}\left(\frac{2 \cdot \pi \cdot i \cdot \operatorname{val}\left(k\right)}{a + b + 2}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.eigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The symbol i in the exponential is the imaginary unit. Natural and real scalars in this expression are cast into the complex numbers.

**Definition 1.2 (The cyclicity class).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \operatorname{sector}\left(a, b, k\right) = \operatorname{eigenspace}\left(\operatorname{U}\left(\mathbb{C}, a, b\right), \operatorname{eigenvalue}\left(a, b, k\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a complex submodule of Space(C,a,b), including the possibility of a zero-dimensional eigenspace.

**Definition 1.3 (Restricted bond operators).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{sectorF}\left(a, b, k, j\right) = \operatorname{restrict}\left(\operatorname{F}\left(\mathbb{C}, a, b, j\right), \operatorname{sector}\left(a, b, k\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each bond sum commutes with U and therefore preserves the eigenspace. The index 2 selects F3, the literal 21 to 12 bond sum.

**Definition 1.4 (The restricted eclectic operator).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; \operatorname{sectorT}\left(a, b, k, xi\right) = \operatorname{restrict}\left(\operatorname{T}\left(\mathbb{C}, a, b, xi\right), \operatorname{sector}\left(a, b, k\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coupled operator also commutes with U. Its restriction is the same linear combination of the three restricted bond sums.

**Definition 1.5 (Universality for every filling with a,b at least two).**

$$(\operatorname{claim}) \Leftrightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (2 \le a) \Rightarrow ((2 \le b) \Rightarrow ((\forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall r \in \mathbb{N},\; \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorT}\left(a, b, k, xi\right))^{r}\right)\right) \le \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorF}\left(a, b, k, 2\right))^{r}\right)\right)) \land (\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{eval}\left(\operatorname{vector3}\left(0, 0, 1\right), P\right) = 1) \land (\forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; (\operatorname{eval}\left(xi, P\right) \ne 0) \Rightarrow (\forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall r \in \mathbb{N},\; \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorT}\left(a, b, k, xi\right))^{r}\right)\right) = \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorF}\left(a, b, k, 2\right))^{r}\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.claim` (`✓ std3`).

*Citation.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

§5, Eq. (5.1), arXiv:2112.04506v1: "we claim a universality hypothesis: The Jordan block spectrum of the eclectic model for generic couplings ξ1, ξ2, ξ3 is identical to that of the hypereclectic model, provided L, M, K satisfy L1 = L−M ≥ K, M1 = M−K ≥ K. (5.1)" Here K = 2, L = a+b+2 and M = b+2, so the two inequalities become a,b at least two. The statement is the power-rank form: all couplings satisfy an upper bound, and a single polynomial for the filling certifies equality simultaneously in every cyclicity class and every natural power. Normalization at the hypereclectic point implies that this polynomial is nonzero.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.eigenvalue`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sector`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorF`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorT`
- Dependency: [D5/S3/Quantum/SpinChains/PolynomialPowerRanks](PolynomialPowerRanks.md)
- Dependency: [D5/S3/Quantum/SpinChains/TwoWallWeights](TwoWallWeights.md)
