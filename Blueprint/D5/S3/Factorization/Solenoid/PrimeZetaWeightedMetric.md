# Prime-Zeta Weighted Metric

## Abstract

The normalized prime-zeta weighted p-adic distance metrizes the hidden-address product.

**Theorem 1.1 (Prime-zeta weighting induces the product topology).**

$$\begin{aligned}\forall s: \mathbb{R}, 1 < s \Rightarrow\\(\forall u: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), \operatorname{primeWeightedDistance}\left(s, u, u\right) = 0) \land\\(\forall u: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), v: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), \operatorname{primeWeightedDistance}\left(s, u, v\right) = \operatorname{primeWeightedDistance}\left(s, v, u\right)) \land\\(\forall u: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), v: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), w: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), \operatorname{primeWeightedDistance}\left(s, u, w\right) \le \operatorname{primeWeightedDistance}\left(s, u, v\right) + \operatorname{primeWeightedDistance}\left(s, v, w\right)) \land\\(\forall u: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), v: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), \operatorname{primeWeightedDistance}\left(s, u, v\right) = 0 \Rightarrow u = v) \land\\(\forall T: \operatorname{Set}\left(\operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right)\right), \operatorname{IsOpenIn}\left(\operatorname{ProductTopology}\left(\operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right)\right), T\right) \Leftrightarrow\\\forall u: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), u \in T, \exists epsilon: \mathbb{R}, 0 < epsilon \land\\\forall v: \operatorname{Pi}\left(p: \operatorname{NatPrimes}\left(\right), \operatorname{PadicInt}\left(p\right)\right), \operatorname{primeWeightedDistance}\left(s, u, v\right) < epsilon \Rightarrow v \in T).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Solenoid/PrimeZetaWeightedMetric.prime_weighted_distance_is_metric_and_induces_product_topology` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the literal product, over all bundled natural primes p, of the p-adic integer rings. No parallel hidden-address alias is introduced.

For a real exponent s greater than one, primeWeightedDistance is the sum of the standard p-adic coordinate distances weighted by p to the power minus s and normalized by the corresponding prime-zeta sum.

The displayed conclusion exposes reflexivity, symmetry, the triangle inequality, separation, and equality between product-open sets and sets locally containing a weighted-distance ball.

Prime-power summability controls the tail, while finitely many p-adic balls control the remaining coordinates. This proves the topology clause directly on the source distance rather than hiding it in a new metric instance.

## References

- Truth anchor: `D5/S3/Factorization/Solenoid/PrimeZetaWeightedMetric.prime_weighted_distance_is_metric_and_induces_product_topology`
