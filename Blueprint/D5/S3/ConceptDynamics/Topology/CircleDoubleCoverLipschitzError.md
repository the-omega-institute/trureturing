# Lipschitz Circle Reconstruction Error

## Abstract

Mean squared chord error for intrinsically Lipschitz selectors of the circle squaring cover, with attainment for L at least one half.

**Definition 1.1 (Squared chord reconstruction error).**

Lean statement: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.circle_error`

*Formalization.* `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.circle_error` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a map s of the angle circle of circumference 2*pi, circle_error(s,x) is the squared complex norm of exp(2i*s(x)) - exp(i*x). The angle-circle metric is intrinsic; this definition uses the complex chord only for error measurement.

**Theorem 1.2 (Uniform lower bound).**

Lean statement: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative L and every circle map s that is L-Lipschitz in the intrinsic quotient metric, normalized Haar mean circle_error(s,x) is at least 2/(2L+1).

Lift s to a real angle theta. Its endpoint displacement is an integral number of turns, so the phase 2*theta(t)-t has odd, nonzero winding. Its derivative is bounded by 2L+1 almost everywhere. The primitive 2*(u-sin(u)) of 2-2*cos(u) converts that winding into a weighted variation of at least 4*pi; normalizing the interval integral by Haar measure yields the stated bound.

**Theorem 1.3 (Attainment at and above one half).**

Lean statement: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.sharpness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each L at least 1/2, an actual circle map is L-Lipschitz in the intrinsic metric and has normalized mean squared complex chord error exactly 2/(2L+1).

Set a=2*pi/(2L+1) and b=2*pi-a. The real lift is t/2 on [0,b] and L*(2*pi-t) on [b,2*pi]. The branches agree at b and the endpoints agree on the circle. The proof checks both the direct and wrapping shortest arcs for global Lipschitz continuity. The error is zero on [0,b]; affine substitution and the primitive give the exact integral on [b,2*pi]. No sharpness statement for 0<L<1/2 is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.circle_error`
- Truth anchor: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.lower_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverLipschitzError.sharpness`
