# Perfect balance forces the Latin-rectangle dimension bound

## Abstract

A direct finite-cut proof of the dimension bound for perfectly balanced Latin rectangles.

**Definition 1.1 (Latin rectangles).**

$$\forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{LatinRectangle}\left(k, n\right) = \operatorname{Subtype}\left(\lambda A: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right). ((\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{FunctionInjective}\left(\operatorname{A}\left(i\right)\right)) \land (\forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{FunctionInjective}\left(\lambda i: \operatorname{Fin}\left(k\right). (\operatorname{A}\left(i, j\right))\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.LatinRectangle` (`✓ std3`).

*Citation.* Zhengyu Li, Vijay Ganesh (2026). *How Unbalanced Must a Latin Rectangle Be?*. DOI: [10.48550/arXiv.2611.06003](https://doi.org/10.48550/arXiv.2611.06003). URL: <https://arxiv.org/abs/2611.06003v1>.

*Commentary.*

The carrier consists of arrays A with k rows and n columns, entries in Fin n, injective in every row and every column. The finite square row maps are bijections. Indices and symbols are zero based; adding one to column labels preserves every distance. Positive sizes are imposed by the result, not by the carrier.

**Definition 1.2 (Symbol positions).**

$$\forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall L \in \operatorname{LatinRectangle}\left(k, n\right),\; \forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{positions}\left(L, i\right) = \operatorname{inverseBijection}\left(\operatorname{val}\left(L, i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.positions` (`✓ std3`).

*Citation.* Zhengyu Li, Vijay Ganesh (2026). *How Unbalanced Must a Latin Rectangle Be?*. DOI: [10.48550/arXiv.2611.06003](https://doi.org/10.48550/arXiv.2611.06003). URL: <https://arxiv.org/abs/2611.06003v1>.

*Commentary.*

The position permutation is the inverse of the bijective row map. Thus A(i,positions(L,i,u)) equals u, and this is exactly the column containing symbol u. The inverse is constructed from row injectivity on the finite carrier, with no assumed coordinate-bijection bridge.

**Definition 1.3 (Pair distance).**

$$\forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall L \in \operatorname{LatinRectangle}\left(k, n\right),\; \forall u \in \operatorname{Fin}\left(n\right),\; \forall v \in \operatorname{Fin}\left(n\right),\; \operatorname{pairDistance}\left(L, u, v\right) = \sum_{i \in \operatorname{Fin}\left(k\right)} (\lvert \operatorname{val}\left(\operatorname{positions}\left(L, i, u\right)\right) - \operatorname{val}\left(\operatorname{positions}\left(L, i, v\right)\right) \rvert)$$

*Formalization.* `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.pairDistance` (`✓ std3`).

*Citation.* Zhengyu Li, Vijay Ganesh (2026). *How Unbalanced Must a Latin Rectangle Be?*. DOI: [10.48550/arXiv.2611.06003](https://doi.org/10.48550/arXiv.2611.06003). URL: <https://arxiv.org/abs/2611.06003v1>.

*Commentary.*

Sum the absolute differences of symbol positions across all rows. Rational arithmetic exactly embeds the integer distances and the rational comparison value k(n+1)/3.

**Definition 1.4 (Total imbalance).**

$$\forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall L \in \operatorname{LatinRectangle}\left(k, n\right),\; \operatorname{imbalance}\left(L\right) = \sum_{u \in \operatorname{Fin}\left(n\right)} (\sum_{v \in \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(u < v, \lvert \operatorname{pairDistance}\left(L, u, v\right) - \frac{k \cdot \left(n + 1\right)}{3} \rvert, 0\right)))$$

*Formalization.* `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.imbalance` (`✓ std3`).

*Citation.* Zhengyu Li, Vijay Ganesh (2026). *How Unbalanced Must a Latin Rectangle Be?*. DOI: [10.48550/arXiv.2611.06003](https://doi.org/10.48550/arXiv.2611.06003). URL: <https://arxiv.org/abs/2611.06003v1>.

*Commentary.*

The double sum keeps only u less than v, so each unordered pair contributes exactly once. Every contribution is nonnegative; zero imbalance therefore gives the same distance k(n+1)/3 for every distinct pair.

**Theorem 1.5 (The full dimension bound).**

$$\forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (0 < k) \Rightarrow ((k \le n) \Rightarrow (\forall L \in \operatorname{LatinRectangle}\left(k, n\right),\; (\operatorname{imbalance}\left(L\right) = 0) \Rightarrow (n \le 2 \cdot k)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhengyu Li, Vijay Ganesh (2026). *How Unbalanced Must a Latin Rectangle Be?*. DOI: [10.48550/arXiv.2611.06003](https://doi.org/10.48550/arXiv.2611.06003). URL: <https://arxiv.org/abs/2611.06003v1>.

*Commentary.*

This is the direct implication in Li–Ganesh, Section 10 open problem (5), for every positive 1 ≤ k ≤ n. The n = 1 case is explicit. For n ≥ 2 choose a first row permutation p and weights a(u)=2 val(p(u))+1−n. Bijection reindexing gives sum a=0 and N=sum a²=n(n²−1)/3. For any coordinate q, the finite-cut identity gives E(q)=−sum over ordered u,v of a(u)a(v)|q(u)−q(v)|=2 sum over cuts of the squared partial weight sum, hence E(q)≥0. In the first row the cut sums are −(j+1)(j+1−n), and Mathlib's rational Faulhaber theorem gives E(p)=n(n⁴−1)/15. Equal pair distances give sum E(q)=k(n+1)N/3. Keeping the first nonnegative row energy yields k(n+1)/3≥(n²+1)/5. For the integer n≥2, (n−2)(n−3)≥0, including the separate n=2 and n=3 cases, yields n≤2k. Column injectivity remains in the original carrier, although the estimate needs only the row bijections. This does not settle the general ℓ1 Kusner conjecture or nonsquare impossibility.

## References

- Truth anchor: `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.LatinRectangle`
- Truth anchor: `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.imbalance`
- Truth anchor: `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.pairDistance`
- Truth anchor: `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.positions`
- Truth anchor: `D5/S3/Combinatorics/Latin/PerfectBalanceDimension.result`
