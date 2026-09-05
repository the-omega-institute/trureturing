# Complexity Density Exchange Rate

## Abstract

Positive limiting complexity densities recover the entropy exchange rate.

**Theorem 1.1 (The density quotient tends to the entropy quotient).**

$$\operatorname{limitAlong}\left(l, \operatorname{ratio}\left(\operatorname{density1}\left(\mathit{index}\right), \operatorname{density2}\left(\mathit{index}\right)\right)\right) = \operatorname{ratio}\left(\mathit{h1}, \mathit{h2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/ComplexityDensityExchangeRate.complexity_density_ratio_tendsto_entropy_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the two complexity-density functions converge along the same filter to the positive tower entropies h1 and h2. Their quotient then converges to h1 divided by h2, which is the claimed height exchange rate.

The source statement invokes Brudno's theorem to supply the two complexity-density limits. This formalization isolates the independent column-reduction step conditionally on those limits; it does not claim a formalization of Kolmogorov complexity or Brudno's theorem.

Both entropies are explicitly positive, preserving the source's positive-entropy regime. In particular h2 is nonzero, avoiding Lean's totalized division-by-zero case. Pinned Mathlib's Filter.Tendsto.div is an exact match and is applied directly.

## References

- Truth anchor: `D5/S0/Naming/ComplexityDensityExchangeRate.complexity_density_ratio_tendsto_entropy_ratio`
