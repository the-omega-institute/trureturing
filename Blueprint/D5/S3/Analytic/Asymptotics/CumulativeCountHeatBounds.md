# Cumulative count heat bounds

## Abstract

Monotone cumulative geometric counts give all positive time summability and two-sided small-time heat bounds.

**Theorem 1.1 (The scalar heat estimate from cumulative counts).**

$$\forall N: \mathbb{N}, \forall cminus, cplus, lambda, q: \mathbb{R}, (\operatorname{Monotone}(N) \land \operatorname{N}(0) = 1 \land 0 < cminus \land 0 < cplus \land 1 < lambda \land 1 < q \land \forall L: \mathbb{N}, cminus \times lambda^{L} \leq \operatorname{NatCast}(\operatorname{N}(L)) \land \operatorname{NatCast}(\operatorname{N}(L)) \leq cplus \times lambda^{L}) \Rightarrow (0 < gamma \land 0 < Cminus \land 0 < Cplus) \land \forall t: \mathbb{R}, 0 < t \Rightarrow \operatorname{Summable}(Ft) \land \forall t: \mathbb{R}, 0 < t \land t \leq 1 \Rightarrow Cminus \times t^{-gamma} \leq \operatorname{S}(t) \land \operatorname{S}(t) \leq Cplus \times t^{-gamma}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/CumulativeCountHeatBounds.cumulative_count_heat_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be a monotone natural-valued cumulative count with N(0)=1. Assume positive constants c_minus and c_plus and bases lambda,q greater than one sandwich every N(L) between c_minus lambda^L and c_plus lambda^L.

Define the natural increments by subtraction, the zero mode a(0)=0 and a(L)=q^L for L>0, and let F_t(L) be the increment weighted by exp(-t a(L)). The exponent gamma is log(lambda)/log(q); U is the convergent superexponential tail sum of lambda^(k+1) exp(-q^k).

For every positive t the scalar series is summable. For 0<t<=1, its sum lies between C_minus t^(-gamma) and C_plus t^(-gamma), where C_minus=c_minus/(exp(1) lambda) and C_plus=c_plus(1+U). The proof uses only cumulative counts, so zero increments and plateaus are allowed.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/CumulativeCountHeatBounds.cumulative_count_heat_bounds`
