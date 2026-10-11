# Hieu's Weak Pareto Connectedness Refutation

## Abstract

Continuous convex objectives on a closed convex strip can have a disconnected weak Pareto solution set.

**Definition 1.1 (Weak Pareto solutions).**

$$\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall K: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)\right), \forall f: \operatorname{Fin}\left(m\right) \mapsto \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right) \mapsto \mathbb{R}, \forall z: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right), z \in \operatorname{weakPareto}\left(K, f\right) \Leftrightarrow (z \in K \land \neg (\exists u: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right), u \in K \land (\forall i: \operatorname{Fin}\left(m\right), \operatorname{At}\left(f, i, u\right) < \operatorname{At}\left(f, i, z\right))))$$

*Formalization.* `D5/S3/Analytic/Convexity/WeakParetoDisconnected.weakPareto` (`✓ std3`).

*Citation.* Vu Trung Hieu (2026). *A connectedness result for convex polynomial multi-objective optimization without boundedness*. URL: <https://arxiv.org/abs/2610.01029v1>.

*Commentary.*

In the Euclidean specialization E=EuclideanSpace ℝ (Fin n), weakPareto K f is a set of points in E. Membership means that the point is feasible and no feasible point is strictly smaller in every objective.

**Definition 1.2 (Connectedness for continuous convex data).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, \forall m: \mathbb{N}, (1 \le n) \Rightarrow ((1 \le m) \Rightarrow (\forall K: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)\right), \forall f: \operatorname{Fin}\left(m\right) \mapsto \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right) \mapsto \mathbb{R}, (\operatorname{Nonempty}\left(K\right)) \Rightarrow ((\operatorname{IsClosed}\left(K\right)) \Rightarrow ((\operatorname{Convex}\left(\mathbb{R}, K\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(m\right), \operatorname{Continuous}\left(\operatorname{At}\left(f, i\right)\right)) \Rightarrow ((\forall i: \operatorname{Fin}\left(m\right), \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{univ}\left(\right), \operatorname{At}\left(f, i\right)\right)) \Rightarrow (\operatorname{IsPreconnected}\left(\operatorname{weakPareto}\left(K, f\right)\right)))))))))$$

*Formalization.* `D5/S3/Analytic/Convexity/WeakParetoDisconnected.claim` (`✓ std3`).

*Citation.* Vu Trung Hieu (2026). *A connectedness result for convex polynomial multi-objective optimization without boundedness*. URL: <https://arxiv.org/abs/2610.01029v1>.

*Commentary.*

Section 4.3 asks verbatim: “whether Sol^w(K,f) is still connected in the general convex case, with K closed convex and the f_i convex and continuous but not necessarily polynomial”. The paper adds: “no explicit example of a disconnected weak Pareto solution set is known” and says that Theorem 1 “shows that no such example can have convex polynomial data”. The formal claim quantifies over nonempty closed convex feasible sets in finite-dimensional Euclidean spaces of dimension at least one, at least one objective, continuous convex objectives, and preconnected weak Pareto solutions.

**Theorem 1.3 (A disconnected weak Pareto solution set).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/WeakParetoDisconnected.result` (`✓ std3`). ∎

*Resolves.* `Problems/hieu-2026-weak-pareto-connectedness` (refuted) by `D5/S3/Analytic/Convexity/WeakParetoDisconnected.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hieu-2026-weak-pareto-connectedness","declaration_gid":"D5/S3/Analytic/Convexity/WeakParetoDisconnected.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vu Trung Hieu (2026). *A connectedness result for convex polynomial multi-objective optimization without boundedness*. URL: <https://arxiv.org/abs/2610.01029v1>.

*Commentary.*

Take K=[0,∞)×[0,2], h(x)=√(x²+1)−x, f₁(x,y)=y², and f₂(x,y)=(max(h(x)−y/2,0))²−y/2. The Lean proof establishes nonemptiness, closedness and convexity of K, continuity and convexity of both objectives, weak Pareto boundary pieces y=0 and y≥2h(x), strict domination throughout 0<y<2h(x), and separation by the open sets y<h(x) and y>h(x). Thus the universal connectedness claim is false without boundedness or a constraint qualification.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/WeakParetoDisconnected.claim`
- Truth anchor: `D5/S3/Analytic/Convexity/WeakParetoDisconnected.result`
- Truth anchor: `D5/S3/Analytic/Convexity/WeakParetoDisconnected.weakPareto`
