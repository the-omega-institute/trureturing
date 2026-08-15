# Capture Count Second Moment

## Abstract

The finite capture count has its exact variance identity and a Paley-Zygmund lower bound.

**Theorem 1.1 (Capture count variance and second-moment lower bound).**

$$mu=\sum_{a}\operatorname{P}(\operatorname{Captured}\left(a\right)) \land \operatorname{Var}(N)=\operatorname{E}(N^{2})-mu^{2} \land (0<\operatorname{E}(N^{2}) \Rightarrow \frac{mu^{2}}{\operatorname{E}(N^{2})}\leq\operatorname{P}(\exists a,\ \operatorname{Captured}\left(a\right))).$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Probability/CaptureSecondMoment.capture_count_variance_and_lower_bound` (`✓ std3`). ∎

*Citation.* R. E. A. C. Paley and A. Zygmund (1932). *A note on analytic functions in the unit circle*. DOI: [10.1017/s0305004100010112](https://doi.org/10.1017/s0305004100010112).

*Commentary.*

Let N count addresses satisfying the frozen Captured predicate in the normalized finite independent-listing model. Its mean mu is the sum of the existing one-address capture probabilities. Its centered variance is E[N^2]-mu^2, and when E[N^2] is positive, the probability of at least one captured address is at least mu^2/E[N^2].

The lower bound is the theta=0 case of the Paley-Zygmund inequality. The Lean proof applies Mathlib's finite Cauchy-Schwarz theorem directly to the weighted count and the indicator of the existing capture event; it does not introduce another capture predicate or probability model.

Pinned-library searches found Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul but no packaged Paley-Zygmund theorem. Repository searches found exact one- and two-address laws and Bonferroni bounds, but no capture-count variance or second-moment lower bound.

## References

- Truth anchor: `D5/S0/Diagonal/Probability/CaptureSecondMoment.capture_count_variance_and_lower_bound`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture](../../Asymptotics/WeightedProbability/FiniteProductCapture.md)
