# The mixed phase term in the disjoint triple sum

## Abstract

One mixed phase term completes the disjoint triple sum for complementary weights.

**Theorem 1.1 (Pair contribution and mixed phase term).**

$$\begin{aligned}&\forall J\quad[\operatorname{Fintype}\left(J\right)]\quad[\operatorname{DecidableEq}\left(J\right)]\quad\forall R\quad[\operatorname{CommRing}\left(R\right)],\\&\forall x,y:J\to R,\quad(\forall j\in J,\operatorname{x}\left(j\right)\operatorname{y}\left(j\right)=1)\implies\\&n=|J|,\quad X=\sum_{j \in J}\operatorname{x}\left(j\right),\quad Y=\sum_{j \in J}\operatorname{y}\left(j\right),\quad X_{2}=\sum_{j \in J}\operatorname{x}\left(j\right)^{2},\quad Y_{2}=\sum_{j \in J}\operatorname{y}\left(j\right)^{2},\\&\operatorname{D}\left(x, y\right) = \left(P_{n}\right)\left(XY\right) - 3(X_{2}Y^{2} + Y_{2}X^{2}),\\&\forall u:R,\quad\left(P_{n}\right)\left(u\right) = u^{3} + (18 - 9n)u^{2} + (18n^{2} - 63n + 51)u\\&\quad- 6n^{3} + 27n^{2} - 31n.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DisjointTriplePhaseIdentity.disjoint_triple_phase_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be finite with n elements, and let x and y take values in a commutative ring. Assume x(j)y(j)=1 for every j. Write X and Y for the sums of x and y, and X₂ and Y₂ for the sums of their squares. The quantity D sums products over ordered pairs of ordered triples with no index shared between the two sides. The triples may repeat indices.

Inclusion and exclusion uses the nine possible equalities between left and right positions. Each subset of equalities partitions the six positions into connected components, and each component has one freely chosen index. A component with a left positions and b right positions contributes the sum of x(j) to the power a times y(j) to the power b. Complementarity cancels the matched powers.

The two types of three-edge star with imbalance of magnitude two have three choices of center on the opposite side and sign minus. They give the terms X₂Y² and Y₂X². The other component profiles yield the polynomial in n and XY.

For unit-weight integer frequencies g, take x(j) and y(j) to be Laurent monomials at exponents g(j) and −g(j). The two extra terms have exponents 2g(i)−g(j)−g(k) and their negatives. Extracting a band selects the corresponding signed frequency differences.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DisjointTriplePhaseIdentity.disjoint_triple_phase_identity`
