# Cumulative count heat bounds

## Abstract

Monotone cumulative geometric counts give all positive time summability and two-sided small-time heat bounds.

**Theorem 1.1 (The scalar heat estimate from cumulative counts).**

$$\forall N: \mathbb{N} \to \mathbb{N}, \forall cminus, cplus, lambda, q: \mathbb{R}, (\operatorname{Monotone}(N) \land \operatorname{N}(0) = 1 \land 0 < cminus \land 0 < cplus \land 1 < lambda \land 1 < q \land (\forall L: \mathbb{N}, (cminus \times lambda^{L} \leq \operatorname{NatCast}(\operatorname{N}(L)) \land \operatorname{NatCast}(\operatorname{N}(L)) \leq cplus \times lambda^{L}))) \Rightarrow ((0 < gamma \land 0 < Cminus \land 0 < Cplus) \land (\forall t: \mathbb{R}, 0 < t \Rightarrow \operatorname{Summable}(F_{t})) \land (\forall t: \mathbb{R}, (0 < t \land t \leq 1) \Rightarrow (Cminus \times t^{-gamma} \leq \operatorname{S}(t) \land \operatorname{S}(t) \leq Cplus \times t^{-gamma}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/CumulativeCountHeatBounds.cumulative_count_heat_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N: Nat -> Nat be a monotone cumulative count with N(0)=1. Assume positive real constants cminus and cplus and real bases lambda,q greater than one sandwich every N(L) between cminus lambda^L and cplus lambda^L. NatCast denotes the inclusion of natural numbers into the reals.

Define m: Nat -> Nat by m(0)=1 and m(k+1)=N(k+1)-N(k) for every natural k, using natural subtraction (truncated at zero). Define a: Nat -> Real by a(0)=0 and a(k+1)=q^(k+1) for every natural k.

For real t and natural L, define F_t(L)=NatCast(m(L))*exp(-t*a(L)), and define S(t) as the infinite sum of F_t(L) over all natural L, including L=0. Set gamma=log(lambda)/log(q). For natural k, put u(k)=lambda^(k+1)*exp(-(q^k)); U is the infinite sum of u(k) over all natural k, including k=0. This superexponential tail series converges. Set Cminus=cminus/(exp(1)*lambda) and Cplus=cplus*(1+U).

For every positive t the scalar series is summable. For 0<t<=1, its sum S(t) lies between Cminus*t^(-gamma) and Cplus*t^(-gamma), with the same constants for all such t and with real powers. The proof uses only cumulative counts, so zero increments and plateaus are allowed.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/CumulativeCountHeatBounds.cumulative_count_heat_bounds`
