# Ancestral collisions and repetition variance

## Abstract

Actual ancestral sources give a degree-independent native repetition variance bound.

Initial opinions and positive-time fresh opinions have disjoint labels. A fresh label records its positive natural birth time and vertex. At time zero the source is the initial coordinate. A refresh selects the corresponding fresh coordinate. A copy follows the actual chosen neighbour into the preceding time layer.

**Theorem 1.1 (Reconstruction of the actual opinion).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall x \in (c:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, c\right),\; \forall n \in \mathbb{N},\; \forall v \in V,\; \forall w \in O,\; \operatorname{nvm}\left(x, n, v, w\right) = \operatorname{coin}\left(x, \operatorname{source}\left(x, n, v, w\right), w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.native_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

For every coordinate assignment, vertex, natural time and sample point, the native opinion equals the coin at its source label. The identity is pathwise and includes time zero.

**Theorem 1.2 (The degree-independent finite-time lower bound).**

$$\forall V \in \operatorname{Type},\; \forall O \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] [\operatorname{MeasurableSpace}\left(O\right)] \forall P \in \operatorname{Measure}\left(O\right),\; \forall M \in \operatorname{Model}\left(G, P\right),\; \forall u \in V,\; \forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \frac{(t:\mathbb{R})}{4} \cdot \left(1 - (1 - (M.\varepsilon:\mathbb{R}))^{d}\right) \le \operatorname{variance}\left(\operatorname{W}\left(M.\operatorname{coordinate}, u, d, t\right), P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.uniform_variance_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

For every instance of the existing native Model, Var(W_t) is at least t(1-(1-epsilon)^d)/4 for every vertex and natural d,t. This includes finite and infinite connected locally finite graphs and uses that model's original probability space and joint coordinate law. The empty time sum and lag zero give a zero lower bound. At lag two the expression is the lower endpoint required by the source Theorem 3.2.

The proof uses deterministic finite source support to establish measurability. The complete source field is independent of the labelled fair opinion coins. Consequently, a two-opinion sign moment is its source-collision probability, and a four-opinion sign moment is the probability of an even pairing of its four sources. The pairing events form a union and can overlap; their probabilities are not added.

Comparing the sign-product covariance with the covariance of the source-collision indicators leaves nonnegative off-diagonal contributions and an unequal-source probability on the diagonal. The variance of the collision-indicator sum is nonnegative. A collision across lag d requires survival without refresh through those d layers, whose probability is (1-epsilon)^d under the actual joint law.

The native Model also prescribes independent fresh, refresh and choice coordinates at time zero. A bridge from every realization prescribing those families only at positive times has not been established here. The result also does not give the K2 finite-time independence and variance identity, construct the full optimal-constant infimum, or prove its upper endpoint, endpoint ratio, polynomial bracket and asymptotic clauses. It makes no assertion about exact-infimum attainment or existence of a normalized limit.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.native_source`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/AncestralSources.uniform_variance_lower`
- Dependency: [D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear](RepetitionVarianceLinear.md)
