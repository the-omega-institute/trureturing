# Classical avoidance and a proper cut

## Abstract

Actual classical 2413/3142 avoidance implies a nonempty proper direct or skew cut.

This is the known classical bridge recorded in Proposition 2.1 of the cited source, with an internal graph proof. It does not settle the real-rootedness assertion in Conjecture 5.2.

**Definition 1.1 (The literal pattern 2413).**

$$\operatorname{pattern2413}=[1,3,0,2]$$

*Formalization.* `D5/S1/Words/Patterns/Separable/ProperCut.pattern2413` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

This permutation of Fin(4) has values 1, 3, 0, 2 at positions 0, 1, 2, 3. The bracket notation lists its values in increasing position order.

**Definition 1.2 (The literal pattern 3142).**

$$\operatorname{pattern3142}=[2,0,3,1]$$

*Formalization.* `D5/S1/Words/Patterns/Separable/ProperCut.pattern3142` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

This permutation of Fin(4) has values 2, 0, 3, 1 at positions 0, 1, 2, 3.

**Theorem 1.3 (A nonempty proper direct or skew cut).**

$$\forall n\in\mathbb{N}, \forall p\in\operatorname{Perm}\left(n\right), (2\le n\land \neg \operatorname{Contains}\left(pattern2413, p\right)\land \neg \operatorname{Contains}\left(pattern3142, p\right))\Rightarrow \exists m\in\mathbb{N}, 1\le m\land m<n\land ((\forall i,j\in\operatorname{Fin}\left(n\right), (i<m\land m\le j)\Rightarrow \operatorname{p}\left(i\right)<\operatorname{p}\left(j\right))\lor (\forall i,j\in\operatorname{Fin}\left(n\right), (i<m\land m\le j)\Rightarrow \operatorname{p}\left(j\right)<\operatorname{p}\left(i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/ProperCut.avoidance_proper_cut` (`✓ std3`). ∎

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

Here Fin(n) consists of the positions 0 through n-1, and Perm(n) is the set of permutations of Fin(n). Contains(q,p) means that some strictly increasing choice of positions in p has exactly the relative value order of q. For every natural n at least two and every permutation p avoiding both literal patterns, there is a natural m with 1 <= m < n such that either p(i) < p(j) for every pair of positions i < m <= j, or p(j) < p(i) for every such pair. Both parts of the cut are nonempty, and all value inequalities are strict. An induced four-vertex path in the inversion graph supplies one of the two forbidden patterns. A maximal disconnected induced subset proves that the graph or its complement is disconnected. A boundary dart makes the root component order-convex, and its least omitted position supplies the cut.

Real-rootedness of the actual-avoider descent polynomials remains unproved here. The source's tree bijection requires the greatest valid cut, standardization, preservation of actual avoidance, and descent correspondence. Those conclusions and the real-rootedness proof are not supplied by this existence theorem.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/ProperCut.avoidance_proper_cut`
- Truth anchor: `D5/S1/Words/Patterns/Separable/ProperCut.pattern2413`
- Truth anchor: `D5/S1/Words/Patterns/Separable/ProperCut.pattern3142`
- Dependency: [D5/S1/Words/Patterns/DerangementRatioNonconvergence](../DerangementRatioNonconvergence.md)
