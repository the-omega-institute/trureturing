# Moving logarithmic prime boxes

## Abstract

Local Abel error and capacity of shrinking logarithmic prime boxes.

**Theorem 1.1 (Finite local Abel bound).**

$$\forall y \in \mathbb{R},\; \forall z \in \mathbb{R},\; \forall E \in \mathbb{R},\; \left(2\leq y \land \left(y\leq z \land (\forall t \in \mathbb{R},\; t\in [y,z] \Rightarrow \lvert \theta(t)-t \rvert \leq E)\right)\right) \Rightarrow \lvert \operatorname{primeIntervalCard}\left(y, z\right)-\int_{y}^{z}\frac{1}{\log(t)}\,d t \rvert \leq \frac{2E}{\log(y)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity.abs_primeInterval_card_sub_integral_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write primeIntervalCard(y,z) for the cardinality of the primes in the real interval (y,z]. Subtract the Abel identities at the two endpoints and use the derivative of t/log(t) to subtract the main integral. The absolute errors at the two endpoints contribute E/log(y)+E/log(z). The integral of the nonnegative kernel 1/(t log(t)^2) contributes at most E(1/log(y)-1/log(z)).

**Theorem 1.2 (Capacity at each fixed positive log power).**

$$\forall C \in \mathbb{R},\; \forall a \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall v \in \mathbb{R},\; \left(0<C \land \left(0<a \land u<v\right)\right) \Rightarrow \lim_{P\to \infty}\frac{\operatorname{primeIntervalCard}\left(P\,\exp(\frac{u}{C\,(\log(P))^{a}}), P\,\exp(\frac{v}{C\,(\log(P))^{a}})\right)}{\frac{\frac{P}{\log(P)}}{C\,(\log(P))^{a}}}=v-u$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity.primeInterval_moving_log_power_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both actual real endpoints, and hence the entire box, eventually lie in [P/2,2P]. Choose an integer N>a and apply the theta error estimate uniformly on this shell. The finite Abel error divided by the counting scale then tends to zero. Monotonicity of 1/log(t) squeezes the main integral between the box width divided by the two endpoint logarithms. Each logarithm is asymptotic to log(P). The normalized width tends to v-u by differentiating exp(tv)-exp(tu) at zero. Positive and reflected negative boxes both follow by choosing the fixed ordered endpoints u,v.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity.abs_primeInterval_card_sub_integral_le`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity.primeInterval_moving_log_power_capacity`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Selection](Selection.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError](../../PriceRecord/UniformThetaShellError.md)
