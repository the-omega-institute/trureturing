# Three-lines interpolation and equality

## Abstract

Scalar three-lines interpolation with propagation of equality to the full right boundary.

**Definition 1.1 (Analytic strip data).**

Lean statement: `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.StripData`

*Formalization.* `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.StripData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

StripData records an entire complex function with a uniform finite norm bound on the closed vertical strip 0≤Re(z)≤1. The data are closed under finite sums, addition and multiplication. Exponentials exp(a z+b) with real slope a have this property, and the API supplies the boundedness required by the three-lines theorem.

**Theorem 1.2 (The scalar interpolation bound and its equality boundary).**

Lean statement: `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.strip_moment_bound_and_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.strip_moment_bound_and_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M>0. A complex function continuous on the closed strip and differentiable in its interior, bounded there, with left boundary norm at most one and right boundary norm at most M, has norm at most M^(Re z) throughout the strip. If equality occurs at a real interior point theta with 0<theta<1, then the norm equals M at every right boundary point 1+iy. The equality argument applies the maximum modulus principle to exp(−z log M) times the function.

**Theorem 1.3 (Rotating phases determine their frequencies).**

Lean statement: `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.rotating_phase_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.rotating_phase_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For complex u,v with u nonzero and real a,b, if u exp(iya)=v exp(iyb) for every real y, then u=v and a=b. Evaluation at zero determines the phase, and equality of derivatives at zero determines the frequency.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.StripData`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.rotating_phase_injective`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/ThreeLinesSchurMoment.strip_moment_bound_and_equality`
