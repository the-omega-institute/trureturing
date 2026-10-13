# The optimal T-parameter is not monotone

## Abstract

The optimal T-parameter need not increase with edge density.

**Definition 1.1 (Monotone selections of maximisers).**

$$claim = (\forall v: \mathbb{N}, \forall G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(v\right)\right), \exists qf: \mathbb{R} \to \mathbb{R}, (\forall beta: \mathbb{R}, beta \in \operatorname{Set}.\operatorname{Icc}\left(0, 1\right) \Rightarrow \left(\operatorname{qf}\left(beta\right) \in \operatorname{Set}.\operatorname{Icc}\left(0, 1\right) \land \operatorname{IsMaxOn}\left((\operatorname{tDens}\left(G, beta\right)), \operatorname{Set}.\operatorname{Icc}\left(0, 1\right), \operatorname{qf}\left(beta\right)\right)\right)) \land \operatorname{MonotoneOn}\left(qf, \operatorname{Set}.\operatorname{Icc}\left(0, 1\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.claim` (`✓ std3`).

*Citation.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Day and Sarkar, §5, p. 14 (arXiv v1), verbatim: “Conjecture 2. For each graph G_l, we have that q(G_l, β) is an increasing function of β.” The optimiser is introduced on pp. 13–14 by sup(q∈[0,1]) t(G_l,T_n^e(q)), followed by “and let q(G_l,β)∈[0,1] be the value of q at which the supremum is attained”. The graph has vertex set Fin v, the real density beta ranges over [0,1], and qf selects a maximiser in [0,1] at every density. MonotoneOn means nondecreasing. This is the weakest selection reading; a refutation also excludes a strictly increasing selection. The density is the literal homomorphism limit defined in ThreeClassHomomorphismLimit.

**Theorem 1.2 (A seven-vertex counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.result` (`✓ std3`). ∎

*Resolves.* `Problems/day-sarkar-2021-t-optimizer-monotonicity` (refuted) by `D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"day-sarkar-2021-t-optimizer-monotonicity","declaration_gid":"D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. N. Day; A. Sarkar (2021). *On a Conjecture of Nagy on Extremal Densities*. DOI: [10.1137/19M1296525](https://doi.org/10.1137/19M1296525). URL: <https://arxiv.org/abs/1910.13465>.

*Commentary.*

Take the graph on Fin 7 with edges 01, 12, 20, 03, 34, 35 and 36. It consists of a triangle and a three-leaf star whose centre is joined to one triangle vertex. At beta = 1/1000000 every maximiser exceeds 7743/10000; at beta = 1/10000 every maximiser is below 7719/10000. Each maximum exists and is unique. Since the density increases and the optimal parameter decreases, no monotone selection can satisfy claim.

Write z = r+y. Splitting on the star centre's class gives the density r z³ + 3 b r³ + y z⁶ + 2 b y r² z³ + b r⁴ beta. For s = √beta and x = z/s, use r = s²(1−x²)/(2(1−sx)) and q = x−s(1−x²)/(2(1−sx)). The coordinate map is strictly increasing on [0,1] for 0<s≤1/100. The rational identity and derivative explicitly require 1−sx≠0; this holds on the intervals used here. The derivative of the density divided by s⁵ is (sx²+s−2x) Q_s(x)/(16(sx−1)⁴), where Q_s is a degree-eight polynomial. Its derivative is positive on [1/2,1]. The density divided by s⁵ is below 83/1000 for x≤1/2, whereas its value at x=3/4 exceeds 9/100 at both densities. Exact sign evaluations place the two roots in (77451/100000,77452/100000) and (77384/100000,77385/100000), respectively. The increasing coordinate map transfers these intervals to disjoint, reversed bounds for q. This conclusion concerns the seven-vertex graph and these two densities; no uniform interval of decrease or assertion for every pendant-star graph is made.

## References

- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.claim`
- Truth anchor: `D5/S3/Combinatorics/ExtremalDensity/NagyOptimizerMonotonicity.result`
- Dependency: [D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit](ThreeClassHomomorphismLimit.md)
