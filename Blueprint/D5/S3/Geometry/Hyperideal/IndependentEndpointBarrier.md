# Independent opposite-edge endpoint barrier

## Abstract

Independent opposite-edge endpoint certificates cannot close degree-eight or degree-nine stars.

The endpoint certificate fixes the opposite coordinate at one and uses neighboring coordinates in [b,2], where 1<b<=2. The result is a local analytic obstruction and does not claim that every corresponding triangulation lacks a geometric realization.

**Theorem 1.1 (The endpoint certificate obstruction).**

$$\forall b \in Real, y \in Real, z \in Real, v \in Real, w \in Real,\; \left(1 < b \land \left(b \le 2 \land \left(1 \le y \land \left(y \le 2 \land \left(b \le y \land \left(1 \le z \land \left(z \le 2 \land \left(b \le z \land \left(1 \le v \land \left(v \le 2 \land \left(b \le v \land \left(1 \le w \land \left(w \le 2 \land b \le w\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(arccos\left(cosine\left(b, y, z, 1, v, w\right)\right) < \frac{2\cdot \pi}{9} \land \left(8\cdot arccos\left(cosine\left(b, y, z, 1, v, w\right)\right) < 2\cdot \pi \land 9\cdot arccos\left(cosine\left(b, y, z, 1, v, w\right)\right) < 2\cdot \pi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/IndependentEndpointBarrier.independent_endpoint_certificate_fails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-b endpoint has cosine (2*b^3+b^2+1)/(2*b^3+3*b^2-1), whose exact difference from 7/9 is 4*(b-2)^2*(b+1)/(9*(2*b^3+3*b^2-1)). Mixed-coordinate monotonicity and cos(2*pi/9)<7/9 give theta<2*pi/9.

Consequently both 8*theta and 9*theta are strictly less than 2*pi. The statement applies only to the independent opposite-edge endpoint certificate; it preserves possible positive lower bounds and other length correlations.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/IndependentEndpointBarrier.independent_endpoint_certificate_fails`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
