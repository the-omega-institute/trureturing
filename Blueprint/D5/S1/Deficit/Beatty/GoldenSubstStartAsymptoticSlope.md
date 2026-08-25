# Golden Substitution-Start Asymptotic Slope

## Abstract

The substitution-start ratios converge to the golden ratio.

**Theorem 1.1 (The substitution-start sequence has golden asymptotic slope).**

$$\operatorname{Tendsto}\left(((v : \mathbb{N}) \mapsto \frac{(\operatorname{goldenSubstStart}(v) : \mathbb{R})}{(v : \mathbb{R})}), atTop, \operatorname{nhds}\left(\varphi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/GoldenSubstStartAsymptoticSlope.golden_subst_start_asymptotic_slope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural indices tending to infinity, the real ratio of the substitution-block start to its index tends to the golden ratio. This is a slope statement about substitution positions, not a counting density.

Unfolding goldenSubstStart gives the index plus the prefix true-letter count. The merged true-letter density tends to the inverse golden ratio, and the identity 1 + phi^-1 = phi gives the stated limit. The ratio rewrite is used only eventually, at positive indices.

## References

- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSubstStartAsymptoticSlope.golden_subst_start_asymptotic_slope`
- Dependency: [D5/S1/Words/GoldenSubstFixed](../../Words/GoldenSubstFixed.md)
