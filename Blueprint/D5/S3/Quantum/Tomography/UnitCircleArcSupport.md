# Certified unit-circle arc support

## Abstract

Retain the unit-circle relation when bounding a complex overlap on a signed-Cayley tube.

**Theorem 1.1 (A nonnegative endpoint dual bounds every point of the minor arc).**

$$\operatorname{UnitMinorArc}(a, b, x, y) \land \operatorname{NonnegativeEndpointDual}(ex, ey, gx, gy, lambda, mu) \Rightarrow\\\operatorname{ProjectionUpperBound}(gx, gy, x, y, lambda, mu, a).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/UnitCircleArcSupport.unit_circle_minor_arc_projection_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotate the lower endpoint to (1,0) and write the upper endpoint as (a,b), where a squared plus b squared equals one, a is nonnegative and b is positive. A unit point (x,y) belongs to the minor arc when y is nonnegative and bx-ay is nonnegative. These hypotheses imply (1+a)x+by is at least 1+a.

Choose either endpoint e=(ex,ey), with nonnegative real multipliers lambda and mu. If gx=lambda ex-mu(1+a) and gy=lambda ey-mu b, the conclusion is gx x+gy y <= lambda-mu(1+a). The proof writes the slack as the sum of lambda times the unit-vector support slack and mu times the circular-cap slack. The circular-cap step follows from an exact polynomial identity, so no numerical angle or extremum solver is assumed.

The research checker uses rational endpoint duals for every relative phase, sums their directional bounds in the same complex plane, and only then bounds the squared modulus. This prevents independent real/imaginary boxes from forgetting unit modulus. The standard Cauchy bound handles a direction whose maximizer is inside the arc. The formal theorem supplies the endpoint-dual component; the Cayley-to-arc adapter, finite interval replay and global cover reflection remain separate obligations. Classical circular-cap geometry is not claimed as new mathematics.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/UnitCircleArcSupport.unit_circle_minor_arc_projection_upper`
- Dependency: [D5/S3/Quantum/Tomography/CayleyCoverAnalysis](CayleyCoverAnalysis.md)
