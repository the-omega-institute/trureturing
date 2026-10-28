# Random exponential product strong law

## Abstract

Products of bounded iid operator exponentials converge almost surely in the strong operator topology.

**Definition 1.1 (The random exponential product).**

$$\forall (\mathbb{k}: \operatorname{Type}), (\forall (e: \operatorname{Type}), (\forall (\alpha: \operatorname{Type}), ([\operatorname{RCLike}\left(\mathbb{k}\right)] [\operatorname{NormedAddCommGroup}\left(e\right)] [\operatorname{NormedSpace}\left(\mathbb{k}, e\right)], \forall (a: (\mathbb{N}) \to ((\alpha) \to (\operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)))), (\forall (n: \mathbb{N}), (\forall (t: \mathbb{R}), (\forall (\omega: \alpha), (\operatorname{D5.S3.Analytic.Probability.RandomExponentialProductSLLN.randomProduct}\left(a, n, t, \omega\right) = \operatorname{List.prod}\left(\operatorname{List.ofFn}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{NormedSpace.exp}\left((((\frac{t}{(n: \mathbb{R})}: \mathbb{R}): \mathbb{k})) \cdot (a\left((i: \mathbb{N})\right)\left(\omega\right))\right))\right)\right))))))))$$

*Formalization.* `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.randomProduct` (`✓ std3`).

*Citation.* Sviatoslav V. Dzhenzher; Vsevolod Zh. Sakbaev (2026). *The Strong Law of Large Numbers for random semigroups on uniformly smooth Banach spaces*. DOI: [10.1007/s43036-025-00481-7](https://doi.org/10.1007/s43036-025-00481-7). URL: <https://arxiv.org/abs/2507.07658v3>.

*Commentary.*

For a scalar field K, a normed space e, an index space alpha, and a family of continuous linear endomorphisms a, randomProduct multiplies the exponentials of the factors t/n times a i omega in increasing Fin n order. The real quotient t/n is explicitly cast into K before scalar multiplication. This is the exponential semigroup product used in the source's semigroup setting (source lines 193–199 and 224–229).

**Definition 1.2 (Almost-sure strong-operator convergence on compact time intervals).**

$$\forall (\mathbb{k}: \operatorname{Type}), (\forall (e: \operatorname{Type}), (\forall (\alpha: \operatorname{Type}), ([\operatorname{RCLike}\left(\mathbb{k}\right)] [\operatorname{NormedAddCommGroup}\left(e\right)] [\operatorname{NormedSpace}\left(\mathbb{k}, e\right)] [\operatorname{CompleteSpace}\left(e\right)] [\operatorname{MeasurableSpace}\left(\alpha\right)], \forall (\mu: \operatorname{Measure}\left(\alpha\right)), ([\operatorname{IsProbabilityMeasure}\left(\mu\right)], letI := \operatorname{NormedAlgebra.restrictScalars}\left(\mathbb{R}, \mathbb{k}, \operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)\right); letI : \operatorname{MeasurableSpace}\left(\operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)\right) := \operatorname{borel}\left(\operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)\right); \forall (a: (\mathbb{N}) \to ((\alpha) \to (\operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)))), ((\forall (i: \mathbb{N}), (\operatorname{AEStronglyMeasurable}\left(a\left(i\right), \mu\right))) \to ((\operatorname{Pairwise}\left(\lambda (i: \mathbb{N}) \mapsto (\lambda (j: \mathbb{N}) \mapsto (\operatorname{IndepFun}\left(a\left(i\right), a\left(j\right), \mu\right)))\right)) \to ((\forall (i: \mathbb{N}), (\operatorname{IdentDistrib}\left(a\left(i\right), a\left(0\right), \mu, \mu\right))) \to (\forall (m: \mathbb{R}), ((\forall (i: \mathbb{N}), (\operatorname{Filter.Eventually}\left(\lambda (\omega: \alpha) \mapsto (\left\lVert a\left(i\right)\left(\omega\right) \right\rVert \le m), \operatorname{MeasureTheory.ae}\left(\mu\right)\right))) \to (\forall (x: e), (\forall (t: \mathbb{R}), (((0: \mathbb{R}) \le t) \to (\operatorname{Filter.Eventually}\left(\lambda (\omega: \alpha) \mapsto (\forall (\varepsilon: \mathbb{R}), (((0: \mathbb{R}) < \varepsilon) \to (\operatorname{Filter.Eventually}\left(\lambda (n: \mathbb{N}) \mapsto (\forall (s: \mathbb{R}), ((s \in \operatorname{Set.Icc}\left((0: \mathbb{R}), t\right)) \to (\left\lVert \left((\operatorname{D5.S3.Analytic.Probability.RandomExponentialProductSLLN.randomProduct}\left(a, n, s, \omega\right)) - (\operatorname{NormedSpace.exp}\left((((s: \mathbb{R}): \mathbb{k})) \cdot (\operatorname{MeasureTheory.integral}\left(\mu, \lambda (z: \alpha) \mapsto (a\left(0\right)\left(z\right))\right))\right))\right)\left(x\right) \right\rVert < \varepsilon))), \operatorname{Filter.atTop}\right)))), \operatorname{MeasureTheory.ae}\left(\mu\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sviatoslav V. Dzhenzher; Vsevolod Zh. Sakbaev (2026). *The Strong Law of Large Numbers for random semigroups on uniformly smooth Banach spaces*. DOI: [10.1007/s43036-025-00481-7](https://doi.org/10.1007/s43036-025-00481-7). URL: <https://arxiv.org/abs/2507.07658v3>.

*Commentary.*

The proposition quantifies a scalar field K satisfying RCLike, a complete normed space e, a measurable index space alpha, a probability measure mu, and an operator-valued sequence a. Each a i is mu-almost-everywhere strongly measurable; the sequence is pairwise independent, identically distributed with a 0, and almost surely bounded by one real m. For every vector x and nonnegative time t, almost every omega satisfies an eventual epsilon estimate uniformly for s in [0,t]. The limit is the exponential of the Bochner integral of a 0, with the real time cast into K. This is the formal reading of the source conjecture (source lines 224–229).

**Theorem 1.3 (The strong law for random exponential products).**

$$\forall (\mathbb{k}: \operatorname{Type}), (\forall (e: \operatorname{Type}), (\forall (\alpha: \operatorname{Type}), ([\operatorname{RCLike}\left(\mathbb{k}\right)] [\operatorname{NormedAddCommGroup}\left(e\right)] [\operatorname{NormedSpace}\left(\mathbb{k}, e\right)] [\operatorname{CompleteSpace}\left(e\right)] [\operatorname{MeasurableSpace}\left(\alpha\right)], \forall (\mu: \operatorname{Measure}\left(\alpha\right)), ([\operatorname{IsProbabilityMeasure}\left(\mu\right)], letI := \operatorname{NormedAlgebra.restrictScalars}\left(\mathbb{R}, \mathbb{k}, \operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)\right); letI : \operatorname{MeasurableSpace}\left(\operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)\right) := \operatorname{borel}\left(\operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)\right); \forall (a: (\mathbb{N}) \to ((\alpha) \to (\operatorname{ContinuousLinearMap}\left(\mathbb{k}, e, e\right)))), ((\forall (i: \mathbb{N}), (\operatorname{AEStronglyMeasurable}\left(a\left(i\right), \mu\right))) \to ((\operatorname{Pairwise}\left(\lambda (i: \mathbb{N}) \mapsto (\lambda (j: \mathbb{N}) \mapsto (\operatorname{IndepFun}\left(a\left(i\right), a\left(j\right), \mu\right)))\right)) \to ((\forall (i: \mathbb{N}), (\operatorname{IdentDistrib}\left(a\left(i\right), a\left(0\right), \mu, \mu\right))) \to (\forall (m: \mathbb{R}), ((\forall (i: \mathbb{N}), (\operatorname{Filter.Eventually}\left(\lambda (\omega: \alpha) \mapsto (\left\lVert a\left(i\right)\left(\omega\right) \right\rVert \le m), \operatorname{MeasureTheory.ae}\left(\mu\right)\right))) \to (\forall (x: e), (\forall (t: \mathbb{R}), (((0: \mathbb{R}) \le t) \to (\operatorname{Filter.Eventually}\left(\lambda (\omega: \alpha) \mapsto (\forall (\varepsilon: \mathbb{R}), (((0: \mathbb{R}) < \varepsilon) \to (\operatorname{Filter.Eventually}\left(\lambda (n: \mathbb{N}) \mapsto (\forall (s: \mathbb{R}), ((s \in \operatorname{Set.Icc}\left((0: \mathbb{R}), t\right)) \to (\left\lVert \left((\operatorname{D5.S3.Analytic.Probability.RandomExponentialProductSLLN.randomProduct}\left(a, n, s, \omega\right)) - (\operatorname{NormedSpace.exp}\left((((s: \mathbb{R}): \mathbb{k})) \cdot (\operatorname{MeasureTheory.integral}\left(\mu, \lambda (z: \alpha) \mapsto (a\left(0\right)\left(z\right))\right))\right))\right)\left(x\right) \right\rVert < \varepsilon))), \operatorname{Filter.atTop}\right)))), \operatorname{MeasureTheory.ae}\left(\mu\right)\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.result` (`✓ std3`). ∎

*Resolves.* `Problems/dzhenzher-sakbaev-2025-random-semigroup-slln` (proved) by `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dzhenzher-sakbaev-2025-random-semigroup-slln","declaration_gid":"D5/S3/Analytic/Probability/RandomExponentialProductSLLN.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sviatoslav V. Dzhenzher; Vsevolod Zh. Sakbaev (2026). *The Strong Law of Large Numbers for random semigroups on uniformly smooth Banach spaces*. DOI: [10.1007/s43036-025-00481-7](https://doi.org/10.1007/s43036-025-00481-7). URL: <https://arxiv.org/abs/2507.07658v3>.

*Commentary.*

The proof first installs the real-scalar algebra structure on the continuous linear endomorphisms and their Borel measurable space. In the subsingleton case every operator sends every vector to zero, so the required estimate is immediate.

In the nontrivial case, the Bochner strong law for the bounded iid operator sequence gives almost-sure convergence of the normalized partial sums to the integral b. The centered sums therefore have a sublinear maximum on every sufficiently large prefix. A deterministic estimate combines the Euler product norm bound, the noncommutative Abel summation identity, and the centered maximum to compare the product of (1+(s/n)a i) with (1+(s/n)b)^n uniformly for s in [0,t].

The exponential Taylor remainder bounds the difference between each exponential factor and its first-order approximation by three quarters of the squared scaled norm. A product perturbation estimate then compares the exponential product with the Euler product, and the same estimate compares the constant Euler product with exp(s b). The three errors are bounded by a term proportional to the centered maximum divided by n and a term proportional to 1/n, so the deterministic uniform estimate tends to zero.

Finally, applying the deterministic estimate on the almost-sure strong-law event gives operator-norm convergence uniformly on the time interval. The continuous-linear-map operator bound converts this to the displayed vector estimate for every x, and the resulting almost-everywhere statement is exactly claim.

## References

- Truth anchor: `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.claim`
- Truth anchor: `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.randomProduct`
- Truth anchor: `D5/S3/Analytic/Probability/RandomExponentialProductSLLN.result`
- Dependency: [D5/S3/Observer/Linear/ExactTaylorObservationRemainder](../../Observer/Linear/ExactTaylorObservationRemainder.md)
- Dependency: [D5/S3/Quantum/AURICOmega/ExponentialTail](../../Quantum/AURICOmega/ExponentialTail.md)
