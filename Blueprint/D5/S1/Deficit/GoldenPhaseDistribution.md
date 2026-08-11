# Golden Phase Deficit Distribution

## Abstract

Uniform golden phases give the exact three-valued deficit frequencies and mean.

**Theorem 1.1 (Uniform golden phase sampling has exact deficit frequencies).**

$$freq(+1) = \frac{1}{2phi^{2}}, freq(-1) = \frac{1}{2phi^{4}}, E(c) = \frac{1}{2phi^{3}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/GoldenPhaseDistribution.limiting_deficit_distribution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive and negative events are the two corner triangles cut from the unit phase square by the deficit thresholds. Their legs have lengths inverse golden ratio and inverse golden ratio squared. Integrating the vertical cross sections gives one half times the square of each leg. The signed expectation is the positive area minus the negative area, which simplifies by the golden quadratic identity to one over twice the golden ratio cubed.

## References

- Truth anchor: `D5/S1/Deficit/GoldenPhaseDistribution.limiting_deficit_distribution`
