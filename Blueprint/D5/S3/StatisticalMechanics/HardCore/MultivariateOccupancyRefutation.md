# A counterexample to the multivariate hard-core occupancy bound

## Abstract

The three-vertex star with fugacities (15,2,2) has expected independent-set size 9/8, below the proposed degree-sequence lower bound 259/230.

**Definition 1.1 (Expected independent-set cardinality).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall lam \in (\operatorname{Fin}\left(n\right))\to \mathbb{R},\; \operatorname{expectedSize}\left(G, lam\right) = \frac{\sum_{S \in \operatorname{configurations}\left(G, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right)\right)} (\operatorname{ofNat}\left(\operatorname{card}\left(S\right)\right) \cdot \prod_{v \in S} (lam\left(v\right)))}{\operatorname{partition}\left(G, \operatorname{univ}\left(\operatorname{Fin}\left(n\right)\right), lam\right)}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.expectedSize` (`✓ std3`).

*Citation.* Ewan Davies; Juspreet Singh Sandhu; Jaehyeon Seo; Brian Tan (2026). *Degree-sequence bounds for independent sets via multivariate local occupancy*. DOI: [10.48550/arXiv.2605.05149](https://doi.org/10.48550/arXiv.2605.05149). URL: <https://arxiv.org/abs/2605.05149v1>.

*Commentary.*

Davies, Sandhu, Seo and Tan, arXiv:2605.05149v1, page 1, Section 1: "For a fugacity vector λ ∈ [0, ∞)^V we define for any I ∈ I(G) the measure" P_{G,λ}(I) = (1/Z_G(λ)) ∏_{v∈I} λ_v, "where Z_G(λ) = Σ_{J∈I(G)} ∏_{v∈J} λ_v is the normalizing constant known as the partition function that makes this a probability measure." Here Fin n labels all vertices; configurations(G,univ(Fin n)) is the existing family of actual independent subsets, partition is its existing product-weight sum, and ofNat embeds cardinality into R. The numerator counts each configuration once per occupied vertex. Division is in R. For positive fugacities the empty configuration gives partition at least one, so this normalized sum is the expectation under the displayed measure.

**Definition 1.2 (The proposed bound on the positive orthant).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall lam \in (\operatorname{Fin}\left(n\right))\to \mathbb{R},\; (\forall v \in \operatorname{Fin}\left(n\right),\; 0 < lam\left(v\right)) \Rightarrow (\sum_{v:\operatorname{Fin}\left(n\right)} (\frac{lam\left(v\right)}{1 + (\operatorname{ofNat}\left(\operatorname{degree}\left(G, v\right)\right) + 1) \cdot lam\left(v\right)}) \le \operatorname{expectedSize}\left(G, lam\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.claim` (`✓ std3`).

*Citation.* Ewan Davies; Juspreet Singh Sandhu; Jaehyeon Seo; Brian Tan (2026). *Degree-sequence bounds for independent sets via multivariate local occupancy*. DOI: [10.48550/arXiv.2605.05149](https://doi.org/10.48550/arXiv.2605.05149). URL: <https://arxiv.org/abs/2605.05149v1>.

*Commentary.*

Davies, Sandhu, Seo and Tan, arXiv:2605.05149v1, page 2, Section 1 after Theorem 1: "Strengthening the conjecture, we believe that the multivariate version should hold for any λ in the positive orthant." "The bound in Theorem 1 is tight by the example of a disjoint union of complete graphs (such that λ is constant on each component), though we believe that the upper bound on the entries of λ can be removed." Lee and Seo, arXiv:2602.02450v2, page 16, Section 5, Occupancy fractions: "Having seen the Davies–Kang conjecture, it seems plausible to look for a strengthening of Theorem 1.1 in terms of occupancy fractions." Their (5.2) reads α_G(t; λ) ≥ (1/|V(G)|) Σ_{v∈V(G)} α_{K_{d_v+1}}(tλ_v), t ∈ R_{≥0}, λ ∈ (R_{≥0})^{V(G)}. At t = 1, multiply by |V(G)| to obtain the displayed claim, with α_{K_{d+1}}(x) = x/(1+(d+1)x) as in (5.1). This encodes the strictly positive orthant proposed by Davies et al., which is a subset of the nonnegative orthant of Lee and Seo. Every n, simple graph and positive fugacity vector is quantified. The anonymous DecidableRel instance supplies adjacency decisions; classical decidability supplies an instance for every graph. The empty graph is also included. The degree is its natural-number degree embedded into R by ofNat; the addition, multiplication and division in the bound are real operations.

**Theorem 1.3 (The three-vertex star refutes the bound).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ewan Davies; Juspreet Singh Sandhu; Jaehyeon Seo; Brian Tan (2026). *Degree-sequence bounds for independent sets via multivariate local occupancy*. DOI: [10.48550/arXiv.2605.05149](https://doi.org/10.48550/arXiv.2605.05149). URL: <https://arxiv.org/abs/2605.05149v1>.

*Acknowledgement.* Joonkyung Lee; Jaehyeon Seo (2026). *Lower bounds for multivariate independence polynomials and their generalisations*. DOI: [10.48550/arXiv.2602.02450](https://doi.org/10.48550/arXiv.2602.02450). URL: <https://arxiv.org/abs/2602.02450v2>.

*Commentary.*

Take Mathlib's starGraph on Fin 3 centered at 0 and set lam(0) = 15, lam(1) = lam(2) = 2. Its independent subsets are exactly the empty set, {0}, {1}, {2} and {1,2}; their product weights are 1,15,2,2,4. The partition is 24 and the cardinality-weighted sum is 27, giving expectedSize = 27/24 = 9/8. The degrees are 2,1,1, so the proposed lower bound is 15/46 + 2/5 + 2/5 = 259/230. The difference expectedSize minus this bound is -1/920. All fugacities are positive, contradicting the universal claim. The restricted small-fugacity theorem and the univariate Davies–Kang conjecture are separate statements.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.expectedSize`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MultivariateOccupancyRefutation.result`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](IndependentPartitionDeletion.md)
