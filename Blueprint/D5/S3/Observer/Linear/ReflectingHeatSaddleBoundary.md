# Reflecting heat saddle on the real boundary

## Abstract

The boundary value of the reflecting heat saddle potential controls the real-axis multiplier.

**Theorem 1.1 (Real-axis cancellation at the saddle).**

Lean statement: `D5/S3/Observer/Linear/ReflectingHeatSaddleBoundary.saddle_real_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ReflectingHeatSaddleBoundary.saddle_real_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imaginary potential determines a holomorphic expression in the saddle square-root variable. Dominated convergence takes its real part to the boundary, including logarithmic singularities inside the integration domain. The angular Green function is the logarithm of the exterior Joukowski radius by the quadratic Mahler measure formula. Comparing it with the boundary value gives the cancellation inequality.

## References

- Truth anchor: `D5/S3/Observer/Linear/ReflectingHeatSaddleBoundary.saddle_real_cancellation`
- Dependency: [D5/S3/Observer/Linear/ReflectingHeatSaddleDensity](ReflectingHeatSaddleDensity.md)
