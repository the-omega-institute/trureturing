# Strong dominance fails for unequal-probability coupon collection

## Abstract

A positive four-label, five-draw counterexample to strong dominance.

**Definition 1.1 (The number of distinct labels).**

$$\forall N \in \mathbb{N},\; \forall p \in \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(N\right)\right),\; \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \operatorname{distinctCountPMF}\left(p, n, k\right) = \sum_{w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(N\right)} (\operatorname{if} (\operatorname{Finset.card}\left(\operatorname{Finset.image}\left(w, \operatorname{Finset.univ}\right)\right) = k) \operatorname{then} (\prod_{j: \operatorname{Fin}\left(n\right)} \operatorname{Convexity.StdSimplex.weights}\left(p\right)\left(w\left(j\right)\right)) \operatorname{else} 0)$$

*Formalization.* `D5/S3/Analytic/Probability/StrongDominanceRefutation.distinctCountPMF` (`✓ std3`).

*Citation.* N. Zoroa; E. Lesigne; M. J. Fernández-Sáez; P. Zoroa; J. Casas (2017). *The coupon collector urn model with unequal probabilities in ecology and evolution*. DOI: [10.1098/rsif.2016.0643](https://doi.org/10.1098/rsif.2016.0643). URL: <https://arxiv.org/abs/1608.00155v1>.

*Commentary.*

Section 3, arXiv v1 p. 7: “Let Yₙ be the random variable representing the number of parasitized hosts after n draws, that is Yₙ=k if there are exactly k parasitized hosts after n draws.” Section 2, pp. 5–6, assigns the cylinder probability pᵢ₁pᵢ₂⋯pᵢₙ to each fixed initial word. Fin N labels hosts from zero, and Fin n labels draws from zero. The standard simplex supplies nonnegative real weights of total one, allowing zero weights. The sum runs over every word, including the unique empty word when n=0; image cardinality counts distinct labels.

**Definition 1.2 (One threshold for the two mass functions).**

$$\forall a \in \mathbb{N} \to \mathbb{R},\; \forall b \in \mathbb{N} \to \mathbb{R},\; \operatorname{StronglyDominates}\left(a, b\right) = (\exists c \in \mathbb{R},\; \forall k \in \mathbb{N},\; (((k: \mathbb{R}) \le c) \Rightarrow (a\left(k\right) \le b\left(k\right))) \land ((c < (k: \mathbb{R})) \Rightarrow (b\left(k\right) \le a\left(k\right))))$$

*Formalization.* `D5/S3/Analytic/Probability/StrongDominanceRefutation.StronglyDominates` (`✓ std3`).

*Citation.* N. Zoroa; E. Lesigne; M. J. Fernández-Sáez; P. Zoroa; J. Casas (2017). *The coupon collector urn model with unequal probabilities in ecology and evolution*. DOI: [10.1098/rsif.2016.0643](https://doi.org/10.1098/rsif.2016.0643). URL: <https://arxiv.org/abs/1608.00155v1>.

*Commentary.*

Definition 8.2, arXiv v1 pp. 28, 30 (published Definition 7.2): “Let X and X′ be two real random variables, defined on probabilities spaces (Ω,P) and (Ω′,P′), respectively, and taking values in a denumerable set D. We say that the random variable X strongly stochastically dominates the random variable X′ if there is a critical value c∈ℝ such that, for any d∈D” followed by “if d≤c, then P(X=d)≤P′(X′=d),” and “if d>c, then P(X=d)≥P′(X′=d).”  Here D is ℕ embedded in ℝ, a and b are the two mass functions, and equality with the real threshold belongs to the lower side. Values beyond the finite support have zero mass.

**Definition 1.3 (The strong-dominance conjecture).**

$$\operatorname{claim} = (\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < N) \Rightarrow ((0 < n) \Rightarrow (\forall p \in \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(N\right)\right),\; \forall q \in \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(N\right)\right),\; (\operatorname{D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.moreMixed}\left((\operatorname{fun} i: \operatorname{Fin}\left(N\right) \mapsto \operatorname{Convexity.StdSimplex.weights}\left(p\right)\left(i\right)), (\operatorname{fun} i: \operatorname{Fin}\left(N\right) \mapsto \operatorname{Convexity.StdSimplex.weights}\left(q\right)\left(i\right))\right)) \Rightarrow (\operatorname{StronglyDominates}\left(\operatorname{distinctCountPMF}\left(p, n\right), \operatorname{distinctCountPMF}\left(q, n\right)\right)))))$$

*Formalization.* `D5/S3/Analytic/Probability/StrongDominanceRefutation.claim` (`✓ std3`).

*Citation.* N. Zoroa; E. Lesigne; M. J. Fernández-Sáez; P. Zoroa; J. Casas (2017). *The coupon collector urn model with unequal probabilities in ecology and evolution*. DOI: [10.1098/rsif.2016.0643](https://doi.org/10.1098/rsif.2016.0643). URL: <https://arxiv.org/abs/1608.00155v1>.

*Commentary.*

Conjecture, arXiv v1 p. 30: “If p≺q, then the random variable Yₙ defined on the probability space (Ω,Pₚ) strongly stochastically dominates the random variable Yₙ defined on the probability space (Ω,$P_{q}$).”

The positive integers N and n are explicit. The existing moreMixed sorts both weight vectors decreasingly, compares every proper prefix and equates the totals. The zero-length prefix adds only 0≤0. The implication has the source direction p≺q.

**Theorem 1.4 (Refutation).**

$$\neg (\forall N \in \mathbb{N},\; \forall n \in \mathbb{N},\; (0 < N) \Rightarrow ((0 < n) \Rightarrow (\forall p \in \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(N\right)\right),\; \forall q \in \operatorname{Convexity.StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(N\right)\right),\; (\operatorname{D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.moreMixed}\left((\operatorname{fun} i: \operatorname{Fin}\left(N\right) \mapsto \operatorname{Convexity.StdSimplex.weights}\left(p\right)\left(i\right)), (\operatorname{fun} i: \operatorname{Fin}\left(N\right) \mapsto \operatorname{Convexity.StdSimplex.weights}\left(q\right)\left(i\right))\right)) \Rightarrow (\operatorname{StronglyDominates}\left(\operatorname{distinctCountPMF}\left(p, n\right), \operatorname{distinctCountPMF}\left(q, n\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/StrongDominanceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. Zoroa; E. Lesigne; M. J. Fernández-Sáez; P. Zoroa; J. Casas (2017). *The coupon collector urn model with unequal probabilities in ecology and evolution*. DOI: [10.1098/rsif.2016.0643](https://doi.org/10.1098/rsif.2016.0643). URL: <https://arxiv.org/abs/1608.00155v1>.

*Commentary.*

Take N=4, n=5, p=(48,48,2,2)/100 and q=(50,46,3,1)/100. Their decreasing prefix numerators are (48,96,98,100) and (50,96,99,100). The mass numerators at k=2 are 7874904000 and 7873379340, and those at k=3 are 1560192000 and 1566757440, all over 100⁵. The strict inequality at 2 forces c<2. Then 3>c requires the opposite of the strict inequality at 3. All four coordinates of each vector are positive. This contradicts the universal one-threshold assertion while making no assertion against ordinary stochastic dominance.

## References

- Truth anchor: `D5/S3/Analytic/Probability/StrongDominanceRefutation.StronglyDominates`
- Truth anchor: `D5/S3/Analytic/Probability/StrongDominanceRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Probability/StrongDominanceRefutation.distinctCountPMF`
- Truth anchor: `D5/S3/Analytic/Probability/StrongDominanceRefutation.result`
- Dependency: [D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance](../../../S0/Certificates/Hypergraphs/OrientationEntropyBalance.md)
- Dependency: [D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing](../../Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.md)
