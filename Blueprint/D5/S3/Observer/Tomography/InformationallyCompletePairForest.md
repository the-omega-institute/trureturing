# Informationally complete pairs and forests

## Abstract

Two finite real random variables determine every probability weight exactly when their joint value map is injective and their bipartite fiber graph is a forest.

**Definition 1.1 (The distribution on an arbitrary set).**

$$\forall (\alpha: \operatorname{Type}*), ([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], (\forall (f: \alpha \to \mathbb{R}), (\forall (\mu: \alpha \to \mathbb{R}), (\forall (\delta: \operatorname{Set}\left(\mathbb{R}\right)), ((\operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution}\left(f, \mu, \delta\right): \mathbb{R}) = \operatorname{Finset.sum}\left(\operatorname{Finset.filter}\left(\lambda (x: \alpha) \mapsto (f\left(x\right) \in \delta), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\alpha\right))\right), \lambda (x: \alpha) \mapsto (\mu\left(x\right))\right))))))$$

*Formalization.* `D5/S3/Observer/Tomography/InformationallyCompletePairForest.distribution` (`✓ std3`).

*Citation.* Stan Gudder (2019). *Finite-Dimensional Convex Effect Algebras*. DOI: [10.48550/arXiv.1912.05110](https://doi.org/10.48550/arXiv.1912.05110). URL: <https://arxiv.org/abs/1912.05110v1>.

*Commentary.*

For a real random variable f on a finite type α and a real weight μ, the value of the distribution on δ is the sum of μ over the points whose f-values lie in δ. This is the distribution in Section 5, lines 435–439 of the TeX source, extended to arbitrary real weights and arbitrary finite types. No measurability restriction is needed on δ because the sum is finite.

**Definition 1.2 (Informational completeness of a pair).**

$$\forall (\alpha: \operatorname{Type}*), ([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], (\forall (f: \alpha \to \mathbb{R}), (\forall (g: \alpha \to \mathbb{R}), ((\operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.IsICPair}\left(f, g\right)) \Leftrightarrow (\forall (\mu: \alpha \to \mathbb{R}), (\forall (\nu: \alpha \to \mathbb{R}), ((\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(\mu\right)) \to ((\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(\nu\right)) \to ((\operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution}\left(f, \mu\right) = \operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution}\left(f, \nu\right)) \to ((\operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution}\left(g, \mu\right) = \operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.distribution}\left(g, \nu\right)) \to (\mu = \nu)))))))))))$$

*Formalization.* `D5/S3/Observer/Tomography/InformationallyCompletePairForest.IsICPair` (`✓ std3`).

*Citation.* Stan Gudder (2019). *Finite-Dimensional Convex Effect Algebras*. DOI: [10.48550/arXiv.1912.05110](https://doi.org/10.48550/arXiv.1912.05110). URL: <https://arxiv.org/abs/1912.05110v1>.

*Commentary.*

The pair f, g is informationally complete if equality of both distributions forces equality of the probability weights μ and ν. Probability means that every weight is nonnegative and the sum of the weights is one. Equality of distributions is equality as functions on all subsets of the real line. This is the definition at line 474 of Section 5 of the TeX source; the finite type α may also be empty or have a single element.

**Definition 1.3 (The bipartite fiber graph).**

$$\forall (\alpha: \operatorname{Type}*), ([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], (\forall (f: \alpha \to \mathbb{R}), (\forall (g: \alpha \to \mathbb{R}), ((\operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.fiberGraph}\left(f, g\right): \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\mathbb{R}, \mathbb{R}\right)\right)) = \operatorname{SimpleGraph.fromRel}\left(\lambda (v: \operatorname{Sum}\left(\mathbb{R}, \mathbb{R}\right)) \mapsto (\lambda (w: \operatorname{Sum}\left(\mathbb{R}, \mathbb{R}\right)) \mapsto (\operatorname{Sum.elim}\left(\lambda (a: \mathbb{R}) \mapsto (\operatorname{Sum.elim}\left(\operatorname{Function.const}\left(\mathbb{R}, \operatorname{False}\right), \lambda (b: \mathbb{R}) \mapsto (\exists (x: \alpha), ((f\left(x\right) = a) \land (g\left(x\right) = b))), w\right)), \operatorname{Function.const}\left(\mathbb{R}, \operatorname{False}\right), v\right)))\right)))))$$

*Formalization.* `D5/S3/Observer/Tomography/InformationallyCompletePairForest.fiberGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Stan Gudder (2019). *Finite-Dimensional Convex Effect Algebras*. DOI: [10.48550/arXiv.1912.05110](https://doi.org/10.48550/arXiv.1912.05110). URL: <https://arxiv.org/abs/1912.05110v1>.

*Commentary.*

The vertices are two tagged copies of the real line. A left vertex a and a right vertex b are adjacent exactly when some x has f(x) = a and g(x) = b. SimpleGraph.fromRel makes this relation symmetric and excludes loops. There are no edges within either tagged copy, and values outside the ranges of f and g are isolated vertices. Several points with the same joint value give the same simple edge; injectivity of the joint value map records the absence of that multiplicity.

**Theorem 1.4 (The forest characterization).**

$$\forall (\alpha: \operatorname{Type}*), ([\operatorname{Fintype}\left(\alpha\right)] [\operatorname{DecidableEq}\left(\alpha\right)], (\forall (f: \alpha \to \mathbb{R}), (\forall (g: \alpha \to \mathbb{R}), ((\operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.IsICPair}\left(f, g\right)) \Leftrightarrow ((\operatorname{Function.Injective}\left(\lambda (x: \alpha) \mapsto ((f\left(x\right), g\left(x\right)))\right)) \land (\operatorname{SimpleGraph.IsAcyclic}\left(\operatorname{D5.S3.Observer.Tomography.InformationallyCompletePairForest.fiberGraph}\left(f, g\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Tomography/InformationallyCompletePairForest.result` (`✓ std3`). ∎

*Resolves.* `Problems/gudder-2019-informationally-complete-pairs` (proved) by `D5/S3/Observer/Tomography/InformationallyCompletePairForest.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gudder-2019-informationally-complete-pairs","declaration_gid":"D5/S3/Observer/Tomography/InformationallyCompletePairForest.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Stan Gudder (2019). *Finite-Dimensional Convex Effect Algebras*. DOI: [10.48550/arXiv.1912.05110](https://doi.org/10.48550/arXiv.1912.05110). URL: <https://arxiv.org/abs/1912.05110v1>.

*Commentary.*

The joint value map is injective exactly when every nonempty intersection of an f-level set and a g-level set is a singleton. This is complementarity in Section 5, lines 507–508 of the TeX source. The equivalence characterizes the IC pairs asked for at line 588: complementarity must be accompanied by acyclicity of the fiber graph. It holds for every finite α, including the empty and singleton cases.

First, two distributions for f are equal if and only if the weights have equal sums on every f-level set. Evaluating the distributions on singletons proves necessity. For sufficiency, group the finite sum over the inverse image of any δ by the finitely many f-values occurring there, and apply equality on each level set.

If the joint value map is not injective, take distinct points x and y with both f(x) = f(y) and g(x) = g(y). The point masses at x and y are distinct probabilities, but each random variable has the same distribution under the two point masses. Thus an IC pair has an injective joint value map.

Assume the joint value map is injective. A trail p from u to v in the fiber graph determines a signed weight w on α. Its f-level sum at a is the indicator of u = Sum.inl(a) minus the indicator of v = Sum.inl(a); its g-level sum at b is the indicator of v = Sum.inr(b) minus the indicator of u = Sum.inr(b). Moreover, w is nonzero exactly at the points whose edges occur in p, and every absolute weight is at most one. To construct w, start with the zero weight on the empty trail. Prepending an edge from left to right adds the point mass with coefficient one at its unique point; prepending an edge from right to left adds the point mass with coefficient minus one. The trail condition keeps that edge out of the tail, so its previous weight is zero. Injectivity identifies its point uniquely, preserving the support description and the absolute bound. The marginal sums telescope to the stated endpoint indicators.

Any nonzero w with absolute weights at most one and zero sums on all f-level sets and g-level sets gives distinct probabilities with equal distributions. Indeed, a nonzero coordinate makes α nonempty. Let n be its cardinality cast from a natural number to a real number, so n is positive. Summing the f-level sums gives total weight zero. Put μ(x) = (1 + w(x))/n and ν(x) = 1/n. The absolute bound makes μ nonnegative, and both total weights are one. The zero level sums make the two distributions agree for f and for g, while a nonzero coordinate of w makes μ and ν distinct.

A cycle is a nonempty closed trail. Its endpoint indicators cancel, so the signed trail weight has zero sums on every level set. Some edge occurs in the cycle, and the exact support description makes this weight nonzero. The preceding perturbation then contradicts informational completeness. Combining this with injectivity proves that every IC pair has an acyclic fiber graph.

Conversely, suppose the joint value map is injective and the fiber graph is acyclic. Let probabilities μ and ν have equal distributions for f and for g. For w = μ − ν, every f-level sum and every g-level sum is zero. Suppose w is nonzero, and retain only the edges arising from points where w is nonzero; call this graph H. It is a subgraph of the fiber graph and hence acyclic. Its edge set is contained in the image of finite α, so H has finitely many edges and is locally finite. A nonzero coordinate supplies an edge of H. Its connected component C contains both tagged endpoints, and is therefore a nontrivial tree with finitely many edges. Such a tree has vertices of degree one; choose one of them, u, with its unique neighbor q.

The edge from u to q comes from a point y with w(y) nonzero. If u is a left vertex a, every other point z in the f-level set at a has weight zero: a nonzero weight would give another neighbor of u in C, so uniqueness of q forces g(z) = g(y), and injectivity then forces z = y. Thus the f-level sum is w(y), contradicting its vanishing. If u is a right vertex, the identical argument uses its g-level set and forces equality of the f-values. Both possibilities contradict w(y) being nonzero. Consequently w = 0, so μ = ν and the pair is IC.

## References

- Truth anchor: `D5/S3/Observer/Tomography/InformationallyCompletePairForest.IsICPair`
- Truth anchor: `D5/S3/Observer/Tomography/InformationallyCompletePairForest.distribution`
- Truth anchor: `D5/S3/Observer/Tomography/InformationallyCompletePairForest.fiberGraph`
- Truth anchor: `D5/S3/Observer/Tomography/InformationallyCompletePairForest.result`
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../../TotalVariation/CycleSingleCutMinimax.md)
