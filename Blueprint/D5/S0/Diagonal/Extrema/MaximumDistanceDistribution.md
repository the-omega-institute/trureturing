# Maximum Row-Distance Distribution

## Abstract

The maximum diagonal row distance has an exact finite distribution function.

**Theorem 1.1 (Maximum row-distance distribution function).**

$$\operatorname{card}\left(\operatorname{maximumDistanceAtMost}\left(f, r\right)\right) = \operatorname{sum}\left(\operatorname{rowDistanceCount}\left(f, j\right), j, 0, r\right)^{\operatorname{card}\left(A\right)}$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Extrema/MaximumDistanceDistribution.maximum_distance_cdf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event maximumDistanceAtMost(f,r) consists of the finite listings whose row distance is at most r at every address. The frozen exact distance-profile count identifies each profile fiber with the product of its rowDistanceCount factors. Summing all bounded profiles factors into identical single-row prefix sums, one for each address, and therefore gives the stated card(A)-th power.

## References

- Truth anchor: `D5/S0/Diagonal/Extrema/MaximumDistanceDistribution.maximum_distance_cdf`
- Dependency: [D5/S0/Diagonal/DistanceProfile](../DistanceProfile.md)
