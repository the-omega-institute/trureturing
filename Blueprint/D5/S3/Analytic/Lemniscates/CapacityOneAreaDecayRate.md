# Capacity-One Area Decay Rate

## Abstract

The closed unit disc together with the isolated point 4 has capacity one and minimal lemniscate area of neither order 1/n nor order 1/log n.

**Definition 1.1 (The finite-point diameter).**

$$\forall K: \operatorname{Set}\left(\mathbb{C}\right), \forall s: \mathbb{N}, \operatorname{pointDiameter}\left(K, s\right) = (\operatorname{sup}_{a \in \left\{a: \operatorname{Fin}\left(s\right)\to \mathbb{C} \mid \forall i: \operatorname{Fin}\left(s\right), a\left(i\right) \in K\right\}} \operatorname{vandermonde}\left(a\right))^{\frac{2}{(\operatorname{ofNat}\left(s\right)) \cdot (\operatorname{ofNat}\left(s\right) - 1)}}$$

*Formalization.* `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.pointDiameter` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

The s-point diameter is the supremum of the Vandermonde products of s-tuples in K, raised to the real power 2/(s(s−1)). The subtraction in the exponent is in ℝ. Repeated entries are allowed and contribute zero products. The capacity argument uses s≥2.

**Definition 1.2 (Transfinite diameter one).**

$$\forall K: \operatorname{Set}\left(\mathbb{C}\right), \operatorname{TransfiniteDiameterOne}\left(K\right) \Leftrightarrow (\operatorname{Tendsto}\left((s: \mathbb{N} \mapsto \operatorname{pointDiameter}\left(K, s\right)), atTop, \operatorname{nhds}\left(1\right)\right))$$

*Formalization.* `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.TransfiniteDiameterOne` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

The finite-point diameters converge to one as s tends to infinity. The paper defines cap as logarithmic capacity, equivalently the transfinite diameter; this predicate expresses the capacity-one condition through that limit.

**Definition 1.3 (Minimal unit-lemniscate area).**

$$\forall K: \operatorname{Set}\left(\mathbb{C}\right), \forall n: \mathbb{N}, \operatorname{minimalArea}\left(K, n\right) = \operatorname{inf}_{p: \operatorname{Polynomial}\left(\mathbb{C}\right), \operatorname{InP}\left(K, n, p\right)} \operatorname{lemniscateArea}\left(p\right)$$

*Formalization.* `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.minimalArea` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

P_n(K) consists of monic degree-n complex polynomials with all roots in K. The infimum is taken over their unit-lemniscate areas, represented by planar Lebesgue volume on ℂ in the extended non-negative reals. The asymptotic claim uses its toReal projection.

**Definition 1.4 (The capacity-one two-rate claim).**

$$claim \Leftrightarrow (\forall K: \operatorname{Set}\left(\mathbb{C}\right), (\operatorname{IsCompact}\left(K\right)) \Rightarrow ((\operatorname{Nonempty}\left(K\right)) \Rightarrow ((\operatorname{TransfiniteDiameterOne}\left(K\right)) \Rightarrow (\operatorname{IsTheta}\left(atTop, (n: \mathbb{N} \mapsto \operatorname{toReal}\left(\operatorname{minimalArea}\left(K, n\right)\right)), (n: \mathbb{N} \mapsto \frac{1}{\operatorname{ofNat}\left(n\right)})\right) \lor \operatorname{IsTheta}\left(atTop, (n: \mathbb{N} \mapsto \operatorname{toReal}\left(\operatorname{minimalArea}\left(K, n\right)\right)), (n: \mathbb{N} \mapsto \frac{1}{\operatorname{log}\left(\operatorname{ofNat}\left(n\right)\right)})\right)))))$$

*Formalization.* `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.claim` (`✓ std3`).

*Citation.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

Beginning of Section 4, verbatim: “This shows that while $\operatorname{vartheta}\left(K\right) = 0$ may hold for all compacts $K$ with $\operatorname{cap}\left(K\right) = 1$, the decay rate of $A_{n}(K)$ is not universal. It will be interesting to determine whether $A_{n}(K)$ can only decay like $\frac{1}{n}$ or $\frac{1}{\operatorname{log}\left(n\right)}$, or whether other rates are possible.”

The claim requires one of the two Θ orders for every nonempty compact set of transfinite diameter one. Each order means both eventual upper and positive lower bounds by constant multiples of the corresponding sequence, along natural degrees tending to infinity.

**Theorem 1.5 (An isolated point gives another decay type).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.result` (`✓ std3`). ∎

*Resolves.* `Problems/ghosh-ramachandran-2026-capacity-one-decay-rate` (refuted) by `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ghosh-ramachandran-2026-capacity-one-decay-rate","declaration_gid":"D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Ghosh; K. Ramachandran (2026). *A note on the Erdős minimal area problem*. DOI: [10.1090/proc/17897](https://doi.org/10.1090/proc/17897). URL: <https://arxiv.org/abs/2604.03036v3>.

*Commentary.*

Take K equal to the closed unit disc together with {4}. Roots of unity have Vandermonde product s^(s/2), while the Vandermonde determinant gives the upper bound s!·4^s≤(4s)^s. Thus 1≤d_s(K)≤exp(2(log 4+log s)/(s−1)) for s≥2, and K has transfinite diameter one. The competitor p(z)=(z^N−1)(z−4)^k is monic of degree N+k with all roots in K. For k≥2 and N≥k(k−2)+1 its unit lemniscate lies in the annulus 1−2^(−k)<|z|<1+2^(−k) together with the disc |z−4|<2^(−(k−2)). The annulus has area 4π·2^(−k), and the disc has area 16π·2^(−2k)≤16π·2^(−k). Setting N=k²+1 gives A_(k²+k+1)(K)≤20π·2^(−k). Multiplying this bound by k²+k+1 gives a limit of zero, excluding an eventual lower bound of order 1/n. Since 1/n=O(1/log n), an eventual lower bound of order 1/log n is excluded as well. The argument answers the two-rate question without an all-degree sharp estimate or a connected example.

## References

- Truth anchor: `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.TransfiniteDiameterOne`
- Truth anchor: `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.claim`
- Truth anchor: `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.minimalArea`
- Truth anchor: `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.pointDiameter`
- Truth anchor: `D5/S3/Analytic/Lemniscates/CapacityOneAreaDecayRate.result`
- Dependency: [D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation](FeketeLemniscateAreaRefutation.md)
