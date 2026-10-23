# The repetition variance of the noisy voter model

## Abstract

Noisy voter repetition counts have a positive linear variance lower bound.

**Definition 1.1 (Independent space-time coordinates).**

$$\begin{aligned}\forall V \in \operatorname{Type},\; \operatorname{Coord}\left(V\right):\operatorname{Type}\\\forall V \in \operatorname{Type},\; \forall v \in V,\; \operatorname{Coord}.\operatorname{initial}\left(v\right):\operatorname{Coord}\left(V\right)\\\forall V \in \operatorname{Type},\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{Coord}.\operatorname{fresh}\left(t, v\right):\operatorname{Coord}\left(V\right)\\\forall V \in \operatorname{Type},\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{Coord}.\operatorname{refresh}\left(t, v\right):\operatorname{Coord}\left(V\right)\\\forall V \in \operatorname{Type},\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{Coord}.\operatorname{choice}\left(t, v\right):\operatorname{Coord}\left(V\right)\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.Coord` (`✓ std3`).

*Citation.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Four constructors index initial opinions, fresh opinions, refresh controls and neighbour choices. Initial coordinates use only a vertex; the other three use a natural time and a vertex.

**Definition 1.2 (The value at each coordinate).**

$$\begin{aligned}\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall v \in V,\; \operatorname{Value}\left(G, \operatorname{Coord}.\operatorname{initial}\left(v\right)\right) = \operatorname{Bool}\\\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{Value}\left(G, \operatorname{Coord}.\operatorname{fresh}\left(t, v\right)\right) = \operatorname{Bool}\\\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{Value}\left(G, \operatorname{Coord}.\operatorname{refresh}\left(t, v\right)\right) = \operatorname{Bool}\\\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{Value}\left(G, \operatorname{Coord}.\operatorname{choice}\left(t, v\right)\right) = \operatorname{Set}.\operatorname{Elem}\left(G.\operatorname{neighborSet}\left(v\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.Value` (`✓ std3`).

*Citation.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Opinions and refresh controls are Bool-valued. A choice at v takes values in the subtype G.neighborSet(v), so it always selects an actual neighbour. Each value type has the discrete measurable space.

**Definition 1.3 (Fair opinions, Bernoulli controls and uniform choices).**

$$\begin{aligned}\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] \forall e \in \operatorname{unitInterval},\; \forall hNbr \in \left(\forall v \in V,\; \exists w \in V,\; G.\operatorname{Adj}\left(v, w\right)\right),\; \forall v \in V,\; \operatorname{coordinateLaw}\left(G, e, hNbr, \operatorname{Coord}.\operatorname{initial}\left(v\right)\right) = \operatorname{bernoulliMeasure}\left(\operatorname{true}, \operatorname{false}, (\frac{1}{2}:\operatorname{unitInterval})\right)\\\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] \forall e \in \operatorname{unitInterval},\; \forall hNbr \in \left(\forall v \in V,\; \exists w \in V,\; G.\operatorname{Adj}\left(v, w\right)\right),\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{coordinateLaw}\left(G, e, hNbr, \operatorname{Coord}.\operatorname{fresh}\left(t, v\right)\right) = \operatorname{bernoulliMeasure}\left(\operatorname{true}, \operatorname{false}, (\frac{1}{2}:\operatorname{unitInterval})\right)\\\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] \forall e \in \operatorname{unitInterval},\; \forall hNbr \in \left(\forall v \in V,\; \exists w \in V,\; G.\operatorname{Adj}\left(v, w\right)\right),\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{coordinateLaw}\left(G, e, hNbr, \operatorname{Coord}.\operatorname{refresh}\left(t, v\right)\right) = \operatorname{bernoulliMeasure}\left(\operatorname{true}, \operatorname{false}, e\right)\\\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] \forall e \in \operatorname{unitInterval},\; \forall hNbr \in \left(\forall v \in V,\; \exists w \in V,\; G.\operatorname{Adj}\left(v, w\right)\right),\; \forall t \in \mathbb{N},\; \forall v \in V,\; \operatorname{coordinateLaw}\left(G, e, hNbr, \operatorname{Coord}.\operatorname{choice}\left(t, v\right)\right) = (\operatorname{PMF}.\operatorname{uniformOfFintype}\left(\operatorname{Set}.\operatorname{Elem}\left(G.\operatorname{neighborSet}\left(v\right)\right)\right)).\operatorname{toMeasure}\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.coordinateLaw` (`✓ std3`).

*Citation.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Section 1, p. 2: “Initially, at time t = 0, all vertices are assigned with independent Bernoulli random variables X₀(u) ∼ Bern(1/2), u ∈ V(G). Then, for every t ∈ ℕ, every u ∈ V(G) (independently of all the other vertices), with probability ε, gets a random opinion Y_t(u) ∼ Bern(1/2), or, with probability 1 − ε, chooses an opinion of one of its neighbors chosen uniformly at random.” The noise parameter e is a member of unitInterval; true means refresh. The neighbour-existence proof supplies the Nonempty argument of PMF.uniformOfFintype. The displayed half is a member of unitInterval.

**Definition 1.4 (The probability model and all its fields).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] \forall O \in \operatorname{Type},\; [\operatorname{MeasurableSpace}\left(O\right)] \forall P \in \operatorname{Measure}\left(O\right),\; \forall p \in \operatorname{IsProbabilityMeasure}\left(P\right),\; \forall c \in G.\operatorname{Connected},\; \forall hNbr \in \left(\forall v \in V,\; \exists w \in V,\; G.\operatorname{Adj}\left(v, w\right)\right),\; \forall e \in \operatorname{unitInterval},\; \forall hp \in 0 < (e:\mathbb{R}),\; \forall hb \in (e:\mathbb{R}) < 1,\; \forall x \in (i:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, i\right),\; \forall hm \in \left(\forall i \in \operatorname{Coord}\left(V\right),\; \operatorname{Measurable}\left(x\left(i\right)\right)\right),\; \forall hi \in \operatorname{iIndepFun}\left(x, P\right),\; \forall hl \in \left(\forall i \in \operatorname{Coord}\left(V\right),\; \operatorname{HasLaw}\left(x\left(i\right), \operatorname{coordinateLaw}\left(G, e, hNbr, i\right), P\right)\right),\; \operatorname{Model}.\operatorname{mk}\left(p, c, hNbr, e, hp, hb, x, hm, hi, hl\right):\operatorname{Model}\left(G, P\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.Model` (`✓ std3`).

*Citation.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Section 1, p. 2: “Consider a connected graph G (not necessarily finite) and a real number ε ∈ (0, 1).” Model.mk lists, in order, the probability-measure proof, connectivity proof, neighbour-existence proof, noise parameter, its strict bounds, the coordinate family, measurability of each coordinate, independence of the whole family and its marginal laws. Local finiteness supplies finite neighbour types. A one-vertex graph with no neighbour is excluded because its uniform copying law is undefined.

**Definition 1.5 (The synchronous noisy voter recursion).**

$$\begin{aligned}\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall O \in \operatorname{Type},\; \forall x \in (i:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, i\right),\; \forall v \in V,\; \forall w \in O,\; \operatorname{nvm}\left(x, 0, v, w\right) = x\left(\operatorname{Coord}.\operatorname{initial}\left(v\right), w\right)\\\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall O \in \operatorname{Type},\; \forall x \in (i:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, i\right),\; \forall k \in \mathbb{N},\; \forall v \in V,\; \forall w \in O,\; \operatorname{nvm}\left(x, k + 1, v, w\right) = \operatorname{if}x\left(\operatorname{Coord}.\operatorname{refresh}\left(k + 1, v\right), w\right) \operatorname{then}x\left(\operatorname{Coord}.\operatorname{fresh}\left(k + 1, v\right), w\right) \operatorname{else}\operatorname{nvm}\left(x, k, \operatorname{Subtype}.\operatorname{val}\left(x\left(\operatorname{Coord}.\operatorname{choice}\left(k + 1, v\right), w\right)\right), w\right)\end{aligned}$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.nvm` (`✓ std3`).

*Citation.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

At time zero the process reads the initial opinion. At time k+1 it reads the fresh opinion when the refresh control is true; otherwise it reads the previous opinion at the selected neighbour. This is the Bool form of Section 1's displayed recursion on p. 2.

**Definition 1.6 (The unnormalised repetition count).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall O \in \operatorname{Type},\; \forall x \in (i:\operatorname{Coord}\left(V\right)) \to O \to \operatorname{Value}\left(G, i\right),\; \forall u \in V,\; \forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{W}\left(x, u, d, t\right) = \lambda w:O \mapsto \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{Icc}\left(1, t\right), \lambda i:\mathbb{N} \mapsto (\operatorname{if}\operatorname{nvm}\left(x, i, u, w\right) = \operatorname{nvm}\left(x, i + d, u, w\right) \operatorname{then}1 \operatorname{else}0:\mathbb{R})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.W` (`✓ std3`).

*Citation.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Section 2.2, p. 5: “For every t, consider ζ_t = I(X_t = X_{t+d}).” W counts these equalities for 1 ≤ i ≤ t. The observation window therefore extends to time t+d. The summand is a real indicator, and no factor 1/t is present.

**Definition 1.7 (Sublinear variance is impossible).**

$$\operatorname{claim} = \left(\forall V \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [G.\operatorname{LocallyFinite}] \forall O \in \operatorname{Type},\; [\operatorname{MeasurableSpace}\left(O\right)] \forall P \in \operatorname{Measure}\left(O\right),\; \forall M \in \operatorname{Model}\left(G, P\right),\; \forall u \in V,\; \forall d \in \mathbb{N},\; (1 \le d) \Rightarrow (\neg (\operatorname{Asymptotics}.\operatorname{IsLittleO}\left(\operatorname{Filter}.\operatorname{atTop}, \lambda t:\mathbb{N} \mapsto \operatorname{variance}\left(\operatorname{W}\left(M.\operatorname{coordinate}, u, d, t\right), P\right), \lambda t:\mathbb{N} \mapsto (t:\mathbb{R})\right)))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

Section 2.2, p. 6: “May Var(ζ₁ + … + ζ_t) be sublinear? We do not have an answer. However, we prove that it is either linear in t or O(ln t).” The answer is encoded by negating little-o of the real sequence t. V is any vertex type, G any connected locally finite graph with a neighbour at every vertex, P any probability model with the stated independent coordinate laws, u any vertex and d any positive natural lag.

**Theorem 1.8 (A linear variance contribution at regularly spaced times).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.result` (`✓ std3`). ∎

*Resolves.* `Problems/benjamini-helman-tov-zhukovskii-2023-noisy-voter-repetition-variance` (proved) by `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"benjamini-helman-tov-zhukovskii-2023-noisy-voter-repetition-variance","declaration_gid":"D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* I. Benjamini, H. Helman Tov and M. Zhukovskii (2023). *Global information from local observations of the noisy voter model on a graph*. DOI: [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637). URL: <https://arxiv.org/abs/2207.01224>.

*Commentary.*

A refresh at u followed by refreshes at every neighbour isolates one fair opinion. Only the repetition terms at r−d and r contain it. Centres r = k(d+1) do not differ by d. Flipping the isolated fair opinions yields orthogonal covariance projections. Requiring one additional refresh at r+d gives a cylinder of probability e^(degree(u)+2); the future fair opinion makes exactly half of this cylinder contribute. Summing gives Var(W) ≥ (e^(degree(u)+2)/2) floor(t/(d+1)), and this contradicts little-o along multiples of d+1. The floor uses natural-number division. The proof works directly with Measure.infinitePi, including infinite locally finite graphs.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.Coord`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.Model`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.Value`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.W`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.coordinateLaw`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.nvm`
- Truth anchor: `D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.result`
- Dependency: [D5/S3/Combinatorics/IsingUniquenessSets](../../Combinatorics/IsingUniquenessSets.md)
