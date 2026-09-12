# Scalar-Row Sublevel Enclosure

## Abstract

Every small-residual point is contained in an explicitly inflated preconditioned Newton row.

**Theorem 1.1 (A scalar mean-value estimate preserves all sublevel points).**

$$PreconditionedSublevelRowEnclosure.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/SublevelRowEnclosure.preconditioned_sublevel_row_enclosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f:E to F have actual Frechet derivative J at every point m+t(x-m), 0<=t<=1. Let observe:E to R and precondition:F to R be continuous linear maps. Suppose the absolute value of observe(x-m)-precondition(J(m+t(x-m))(x-m)) is bounded by radius along this segment, and norm(f(x))<=eta. Then the distance from observe(x) to observe(m)-precondition(f(m)) is at most radius+norm(precondition)*eta.

The proof composes the actual derivative with the segment map and applies Mathlib's scalar mean-value norm inequality. Each output row may use its own scalar estimate. No common intermediate point for a vector-valued mean-value equality is assumed. The residual inflation is essential; setting it to zero would only certify exact roots.

The interval implementation can discharge the directional bound by enclosing each row of (I-CJ) times the box displacement. This theorem certifies the analytic row inequality only. It does not by itself certify interval arithmetic, the concrete rational residual derivative, the complete subdivision tree, or any external JSON verdict. The source has not been locally elaborated.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/SublevelRowEnclosure.preconditioned_sublevel_row_enclosure`
- Dependency: [D5/S3/Quantum/Tomography/CayleyCoverAnalysis](CayleyCoverAnalysis.md)
