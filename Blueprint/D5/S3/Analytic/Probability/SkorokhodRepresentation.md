# Skorokhod representation on a fixed unit interval

## Abstract

Weak convergence of Polish Borel probability laws admits a full-sequence almost-sure realization on one fixed unit interval.

PolishBorel(X) denotes a topological space equipped with PolishSpace X, MeasurableSpace X and BorelSpace X. The carrier X may belong to any universe. ProbabilityMeasure X has its native topology of weak convergence. The notation measure(rho) denotes the underlying measure of a probability law. Throughout, lambda is the same measure volume.restrict(Set.Icc(0,1)) on the real line, and map(f,lambda) denotes its pushforward by f. AE(lambda) means lambda-almost everywhere.

**Theorem 1.1 (Exact laws and almost-sure convergence of the full sequence).**

$$\begin{aligned}\forall u, \forall X: \operatorname{Type}\left(u\right), \operatorname{PolishBorel}\left(X\right) \Rightarrow\\\forall mu: \mathbb{N} \to \operatorname{ProbabilityMeasure}\left(X\right), \forall mu0: \operatorname{ProbabilityMeasure}\left(X\right), \operatorname{Tendsto}\left(mu, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(mu0\right)\right) \Rightarrow\\\exists Y: \mathbb{N} \to \mathbb{R} \to X, \exists Y0: \mathbb{R} \to X,\\(\forall n: \mathbb{N}, \operatorname{Measurable}\left(\operatorname{Y}\left(n\right)\right)) \land \operatorname{Measurable}\left(Y0\right) \land\\(\forall n: \mathbb{N}, \operatorname{map}\left(\operatorname{Y}\left(n\right), lambda\right) = \operatorname{measure}\left(\operatorname{mu}\left(n\right)\right)) \land\\\operatorname{map}\left(Y0, lambda\right) = \operatorname{measure}\left(mu0\right) \land\\\operatorname{AE}\left(lambda\right) t: \mathbb{R}, \operatorname{Tendsto}\left(n \mapsto \operatorname{Y}\left(n, t\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{Y0}\left(t\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SkorokhodRepresentation.skorokhod_representation` (`✓ std3`). ∎

*Citation.* Unattributed source file; copyright Meta Platforms, Inc. and affiliates (2026). *Strassen coupling, compact Kantorovich duality and Skorokhod representation in ATLAS Lean*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Probability/StrassenCoupling.lean>.

*Commentary.*

The limit law supplies nonemptiness of X. A countable family of arbitrarily small balls with limit-law-null frontiers gives each point a Boolean address. Coordinates are continuous away from the union of those frontiers, and convergence of addresses forces convergence in X. Composing with the inverse of the canonical Cantor-set homeomorphism and subtype inclusion gives a measurable real embedding that is continuous almost everywhere for the limit law and reflects sequence convergence.

For each pushed-forward real law, use the adopted generalized inverse quantile. Portmanteau convergence on continuity sets gives convergence of the distribution functions at all limit-law-null singletons. At every interior continuity point of the limiting raw quantile, the quantile sequence converges. The limiting quantile has only countably many interior discontinuities. The endpoint and countable exceptional sets have Lebesgue measure zero.

The raw quantiles are almost everywhere measurable on the open unit interval. Equality of the open-interval and closed-interval restricted Lebesgue measures transfers this property to lambda. Globally measurable representatives preserve the exact pushforward laws by almost-everywhere equality. Intersect the representative-equality events for every natural index and the limit, all corresponding embedding-range events, and quantile convergence into one conull event. A measurable extension of the embedding inverse produces the copies; convergence reflection gives their full-sequence almost-sure convergence.

The copies have the specified individual laws. The statement asserts no preservation of original cross-index dependence, filtration, adaptedness, independence or conditional laws, and gives no convergence of original variables, algorithm or rate. It assumes no compact or finite support, moments, densities, atomlessness, subsequence, supplied joint law or supplied realization.

The proof source is facebookresearch/atlas-lean, revision a60759060b5616df0d5775b42da4d337719feb32, MathlibExt/Probability/SkorokhodRepresentation.lean. It retains the Meta Platforms copyright and the complete supplier license, including its intended-use preface, at docs/reports/lovasz-suppliers/atlas-LICENSE.txt. This is an adaptation of a known classical theorem and an existing external formalization; no mathematical originality or first-formalization claim is made.

## References

- Truth anchor: `D5/S3/Analytic/Probability/SkorokhodRepresentation.skorokhod_representation`
- Dependency: [D5/S3/Analytic/Probability/CompactQuantile](CompactQuantile.md)
