# A facet of every lazy two-causal polytope

## Abstract

The lazy two-causal inequality J1 induces a facet for every party count at least two.

**Definition 1.1 (A deterministic lazy two-causal strategy).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(k: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \left(\forall \left(f: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.IsLazyTwoCausalStrategy}\left(k, f\right)\right) \Leftrightarrow \left(\left(\operatorname{Finset.Nonempty}\left(k\right)\right) \land \left(\left(k \ne \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right) \land \left(\left(\forall \left(t: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \left(\left(f\left(t\right)\right) \subseteq \left(t\right)\right)\right) \land \left(\forall \left(t: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \left(\forall \left(u: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \left(\left(\operatorname{Inter.inter}\left(t, k\right) = \operatorname{Inter.inter}\left(u, k\right)\right) \to \left(\operatorname{Inter.inter}\left(f\left(t\right), k\right) = \operatorname{Inter.inter}\left(f\left(u\right), k\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.IsLazyTwoCausalStrategy` (`✓ std3`).

*Citation.* Alastair A. Abbott, Julian Wechs, Fabio Costa and Cyril Branciard (2017). *Genuinely multipartite noncausality*. DOI: [10.22331/q-2017-12-14-39](https://doi.org/10.22331/q-2017-12-14-39). URL: <https://arxiv.org/abs/1708.07663v2>.

*Commentary.*

Represent a binary input by its support t and a binary output by its support f(t), both finite subsets of Fin n. The first group k must be nonempty and proper. Laziness means f(t) is contained in t. The outputs in k depend only on the inputs in k: equal intersections of t and u with k give equal intersections of f(t) and f(u) with k. The complementary group may depend on the entire input. This is the deterministic specialization of Definition 2, combined with the lazy output convention (genuine_multi_noncausal.tex, lines 146–154 and 213–214).

**Definition 1.2 (The convex hull of deterministic correlations).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.twoCausalPolytope}\left(n\right): \operatorname{Set}\left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right)\right) = \operatorname{convexHull}\left(\mathbb{R}, \{\left(p: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right) \mid \left(\exists \left(k: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \left(\exists \left(f: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.IsLazyTwoCausalStrategy}\left(k, f\right)\right) \land \left(p = \operatorname{D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift.labelKernel}\left(f\right)\right)\right)\right)\right)\}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.twoCausalPolytope` (`✓ std3`).

*Citation.* Alastair A. Abbott, Julian Wechs, Fabio Costa and Cyril Branciard (2017). *Genuinely multipartite noncausality*. DOI: [10.22331/q-2017-12-14-39](https://doi.org/10.22331/q-2017-12-14-39). URL: <https://arxiv.org/abs/1708.07663v2>.

*Commentary.*

A table p(t,a) gives the probability of output support a at input support t. The deterministic table labelKernel f has entry one when f(t) = a and zero otherwise. Taking the real convex hull over every first group k and every strategy f gives the lazy two-causal polytope. Its tables are nonnegative, sum to one for each input, and vanish unless a is contained in t. Definition 2 gives the convex decomposition; the deterministic description is stated in genuine_multi_noncausal.tex, lines 225–227. The definition also applies to n below two, when there is no nonempty proper first group.

**Definition 1.3 (The first generalized causal functional).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(p: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.jOne}\left(p\right): \mathbb{R}\right) = \left(\operatorname{Finset.sum}\left(\operatorname{Finset.filter}\left(\lambda \left(k: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \mapsto \left(\left(\operatorname{Finset.Nonempty}\left(k\right)\right) \land \left(k \ne \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\right), \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\right), \lambda \left(k: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \mapsto \left(p\left(k, k\right)\right)\right)\right) - \left(p\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.jOne` (`✓ std3`).

*Citation.* Alastair A. Abbott, Julian Wechs, Fabio Costa and Cyril Branciard (2017). *Genuinely multipartite noncausality*. DOI: [10.22331/q-2017-12-14-39](https://doi.org/10.22331/q-2017-12-14-39). URL: <https://arxiv.org/abs/1708.07663v2>.

*Commentary.*

Sum p(k,k) over all nonempty proper input supports k, then subtract the full-input, full-output probability. For a lazy table, at input support k every output outside k is zero. Thus p(k,k) is exactly the marginal probability that every party in k outputs one. This is J₁(n) from inequality (10) (genuine_multi_noncausal.tex, lines 333–337). The functional is defined on every real table.

**Definition 1.4 (Validity and a face of codimension one).**

$$\left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(\left(2: \mathbb{N}\right) \le n\right) \to \left(\left(\forall \left(p: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(p \in \operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.twoCausalPolytope}\left(n\right)\right) \to \left(\left(0: \mathbb{R}\right) \le \operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.jOne}\left(p\right)\right)\right)\right) \land \left(\left(\operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{CoeSort.coe}\left(\operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{Inter.inter}\left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.twoCausalPolytope}\left(n\right), \{\left(p: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right) \mid \left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.jOne}\left(p\right) = \left(0: \mathbb{R}\right)\right)\}\right)\right)\right)\right)\right) + \left(\left(1: \mathbb{N}\right)\right) = \operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{CoeSort.coe}\left(\operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.twoCausalPolytope}\left(n\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alastair A. Abbott, Julian Wechs, Fabio Costa and Cyril Branciard (2017). *Genuinely multipartite noncausality*. DOI: [10.22331/q-2017-12-14-39](https://doi.org/10.22331/q-2017-12-14-39). URL: <https://arxiv.org/abs/1708.07663v2>.

*Commentary.*

For each natural n at least two, J₁ is nonnegative on the entire lazy two-causal polytope, and its zero face has affine dimension one less than the polytope. Here vectorSpan is the linear span of differences of points, so its real finrank is the affine dimension for these nonempty sets. The dimensions and the added one are natural numbers. This expresses the all-party facet question in genuine_multi_noncausal.tex, lines 343–344; it concerns the lazy binary scenario and J₁ alone.

**Theorem 1.5 (The inequality is facet inducing for every n at least two).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\left(2: \mathbb{N}\right) \le n\right) \to \left(\left(\forall \left(p: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right), \left(\left(p \in \operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.twoCausalPolytope}\left(n\right)\right) \to \left(\left(0: \mathbb{R}\right) \le \operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.jOne}\left(p\right)\right)\right)\right) \land \left(\left(\operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{CoeSort.coe}\left(\operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{Inter.inter}\left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.twoCausalPolytope}\left(n\right), \{\left(p: \left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) \to \left(\mathbb{R}\right)\right)\right) \mid \left(\operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.jOne}\left(p\right) = \left(0: \mathbb{R}\right)\right)\}\right)\right)\right)\right)\right) + \left(\left(1: \mathbb{N}\right)\right) = \operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{CoeSort.coe}\left(\operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.twoCausalPolytope}\left(n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.result` (`✓ std3`). ∎

*Resolves.* `Problems/abbott-wechs-costa-branciard-2017-lazy-two-causal-j-one-facet` (proved) by `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abbott-wechs-costa-branciard-2017-lazy-two-causal-j-one-facet","declaration_gid":"D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alastair A. Abbott, Julian Wechs, Fabio Costa and Cyril Branciard (2017). *Genuinely multipartite noncausality*. DOI: [10.22331/q-2017-12-14-39](https://doi.org/10.22331/q-2017-12-14-39). URL: <https://arxiv.org/abs/1708.07663v2>.

*Commentary.*

The defining finite sum makes J₁ a real linear functional. For n ≥ 2, a singleton provides a nonempty proper first group. Consider a deterministic strategy f with first group k. If f sends the full input support to the full output support, independence of the first group's outputs from the complementary inputs forces f(k) = k, using laziness to exclude outputs outside k. Consequently its full-input, full-output probability is at most p(k,k). All diagonal probabilities are nonnegative, and the sum defining J₁ includes this term. Thus J₁ ≥ 0 at every deterministic strategy. The nonnegative half-space of a linear functional is convex, so the inequality holds throughout the convex hull.

Every table in the polytope vanishes at (t,a) when a is not contained in t, and each row sums to one; both conditions hold for deterministic tables and are preserved by convex combinations. Differences of tables therefore vanish at the same forbidden coordinates and have row sums zero. Restrict such a difference to the coordinates (t,a) with a nonempty and contained in t. This restriction is injective: forbidden coordinates are already zero, and the empty-output coordinate in each row is determined by its zero row sum. If r is the number of these coordinates, the direction space of the polytope has dimension at most r.

Let Z be the deterministic correlation whose output support is always empty. It is two-causal for any nonempty proper first group and has J₁(Z) = 0. For nonempty a strictly contained in t, let V indexed by (t,a) output a exactly at input t and the empty set at every other input. Choose the complement of a as its first group; this group is nonempty and proper, and its outputs are always zero. Laziness follows from a being contained in t. Every nonempty diagonal probability vanishes, including the full-input, full-output probability, so V also lies on the zero face.

For a nonempty proper group k, define a further strategy B indexed by k. At input t it outputs k if k is contained in t, and otherwise gives no outputs in k; it additionally outputs the complement of k exactly when t is the full support. These outputs are lazy, and those in k depend only on t intersected with k. At full input it outputs the full support. Among nonempty proper diagonal coordinates its only nonzero entry is p(k,k) = 1. The positive sum and the subtracted term are therefore both one, placing B on the zero face.

Index face points by all r reduced coordinates except the full-input, full-output pair. Use B indexed by t when a = t, and V indexed by (t,a) when a differs from t. Subtract Z from each point. For an off-diagonal index, its difference has value one at its own reduced coordinate and zero at every other indexed coordinate. At any proper diagonal coordinate (k,k), the difference indexed by (k,k) is one and all other differences are zero. In a linear relation, evaluation first at these diagonal coordinates makes all diagonal coefficients zero. Evaluation at each off-diagonal coordinate then makes the remaining coefficients zero. The differences are linearly independent.

For n ≥ 2 the omitted full pair is a reduced coordinate, so the number m of face points satisfies m + 1 = r. Each of the m independent differences belongs to the direction space of the zero face, since both its endpoints lie there. The face dimension is therefore at least m.

The identity strategy f(t) = t is two-causal. Its J₁ value is the number of nonempty proper groups minus one. Any such group and its complement are distinct nonempty proper groups, so this value is strictly positive. Differences of points on the zero face lie in the kernel of J₁. The identity correlation minus Z belongs to the polytope's direction space and has positive J₁ value, so it does not belong to the face's direction space. The latter is thus a proper subspace, and its dimension plus one is at most the polytope dimension.

Combine the upper bound r for the polytope dimension, the lower bound m for the face dimension, the identity m + 1 = r, and the strict dimension inequality. They force the face dimension plus one to equal the polytope dimension. Together with validity, this proves the stated facet property for every n ≥ 2.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.IsLazyTwoCausalStrategy`
- Truth anchor: `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.jOne`
- Truth anchor: `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.result`
- Truth anchor: `D5/S3/Quantum/Contextuality/LazyTwoCausalJOneFacet.twoCausalPolytope`
- Dependency: [D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift](../../TotalVariation/Equality/FiberwiseEqualDistanceLift.md)
