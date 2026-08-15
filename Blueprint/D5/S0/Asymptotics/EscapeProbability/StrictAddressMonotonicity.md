# Strict Address Monotonicity

## Abstract

A fixed point makes frozen escape probability strictly increase with positive address count.

**Theorem 1.1 (A fixed point gives strict monotonicity in positive address count).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y \to Y, 2 \leq \operatorname{card}\left(Y\right) \Rightarrow 0 < \operatorname{card}\left(\operatorname{Fix}\left(f\right)\right) \Rightarrow \operatorname{StrictMonoOn}\left((A \mapsto \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right)), \operatorname{Ici}\left(1\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/StrictAddressMonotonicity.escape_probability_strictMonoOn_of_has_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty output type Y with at least two elements, if f has at least one fixed point, then its frozen escape probability is strictly increasing as the positive address count grows.

The proof applies the public frozen closed form at consecutive address counts. A strict auxiliary ratio comparison uses the positive fixed-point count, and pinned Mathlib's strictMonoOn_of_lt_succ promotes the successor inequality to strict monotonicity on Ici 1.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/StrictAddressMonotonicity.escape_probability_strictMonoOn_of_has_fixed_point`
- Dependency: [D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit](PoissonDomainLimit.md)
- Dependency: [D5/S0/Asymptotics/EscapeProbabilityMonotone](../EscapeProbabilityMonotone.md)
