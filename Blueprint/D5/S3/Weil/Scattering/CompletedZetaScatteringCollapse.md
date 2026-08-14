# Completed-Zeta Scattering Collapse

## Abstract

The completed-zeta functional equation collapses the global scattering quotient.

**Theorem 1.1 (The completed-zeta scattering quotient equals one).**

$$\forall s\in \mathbb{C},\ \operatorname{completedZetaReading}(s) \neq 0 \Rightarrow \frac{\operatorname{completedZetaReading}(1-s)}{\operatorname{completedZetaReading}(s)} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/CompletedZetaScatteringCollapse.completed_zeta_scattering_quotient_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex parameter, the completed-zeta functional equation identifies the reflected numerator with the denominator. When that denominator is nonzero, division therefore gives one.

The nonzero hypothesis is essential because Lean division is total. The frozen critical-line norm theorem remains the separate specialized statement and is not duplicated here.

## References

- Truth anchor: `D5/S3/Weil/Scattering/CompletedZetaScatteringCollapse.completed_zeta_scattering_quotient_eq_one`
- Dependency: [D5/S3/Weil/Scattering/CompletedZetaScatteringQuotient](CompletedZetaScatteringQuotient.md)
