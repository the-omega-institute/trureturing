# Fixed-Output Escape Limit

## Abstract

For a fixed finite output alphabet of size at least two, escape probability tends to one as the address count grows.

**Theorem 1.1 (Fixed-output escape probability tends to one).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y\to Y, 2 \leq \operatorname{card}\left(Y\right) \Rightarrow \lim_{A \to \infty}\operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/FixedOutputLimit.fixed_output_large_address_escape_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact escaped-listing cardinality rewrites the uniform escape ratio into the frozen closed form. The existing escape-ratio limit then gives convergence to one for every fixed finite output alphabet with at least two symbols.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/FixedOutputLimit.fixed_output_large_address_escape_probability`
- Dependency: [D5/S0/Asymptotics/FixedPointFreeEscapeProbability](../FixedPointFreeEscapeProbability.md)
- Dependency: [D5/S0/Diagonal/EscapeAsymptotics](../../Diagonal/EscapeAsymptotics.md)
