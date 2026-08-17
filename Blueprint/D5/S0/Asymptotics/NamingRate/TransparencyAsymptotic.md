# Naming Rate Transparency Asymptotic

## Abstract

The transparency of the Massar-Popescu naming rate is asymptotic to one over the sample count.

**Theorem 1.1 (The scaled naming-rate transparency tends to one).**

$$\lim_{n\to\infty} n\left(1-\frac{n+1}{n+2}\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/NamingRate/TransparencyAsymptotic.naming_rate_transparency_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the naming rate F(n) = (n + 1) / (n + 2), the transparency is 1 - F(n). Multiplying it by n gives a sequence tending to one, which states precisely that the transparency decays asymptotically as 1 / n.

Pinned Mathlib supplies tendsto_natCast_div_add_atTop. The Lean proof rewrites the scaled transparency to n / (n + 2) and applies that theorem directly, without reproving the library limit.

This deposit closes only the naming-rate asymptotic sentence in source remark 27.759 clause 2. The entropy closed forms and the interpretation of the N = 1 value in the same clause remain outside this closure.

## References

- Truth anchor: `D5/S0/Asymptotics/NamingRate/TransparencyAsymptotic.naming_rate_transparency_asymptotic`
