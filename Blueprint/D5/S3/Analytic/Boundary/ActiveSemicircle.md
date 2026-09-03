# Active Semicircle

## Abstract

A reflected rational response is negative exactly inside an active semicircle and diverges negatively at its right-half-plane pole.

**Definition 1.1 (The reflected rational response).**

Lean statement: `D5/S3/Analytic/Boundary/ActiveSemicircle.activeSemicircleResponse`

*Formalization.* `D5/S3/Analytic/Boundary/ActiveSemicircle.activeSemicircleResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The response adds the two reflected first-order rational terms with centers at horizontal coordinates delta and minus delta.

**Theorem 1.2 (Negativity is exactly the open semicircle).**

$$\forall delta \in \operatorname{Real}\left(\right), gamma \in \operatorname{Real}\left(\right), x \in \operatorname{Real}\left(\right), t \in \operatorname{Real}\left(\right),\; \left(0 < delta \land \left(0 < x \land (x - delta)^{2} + (t - gamma)^{2} \ne 0\right)\right) \Rightarrow \left(activeSemicircleResponse\left(delta, gamma, x, t\right) < 0 \Leftrightarrow (x)^{2} + (t - gamma)^{2} < (delta)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source statement is made analytically well-formed by requiring positive delta, positive horizontal coordinate x, and a nonzero pole denominator. The last premise prevents Lean's totalized division by zero from silently assigning a value at the pole.

A common denominator is strictly positive on this domain. Its numerator factors as two times x times the signed radial defect, so the response is negative exactly when the point is inside the circle of radius delta centered at the boundary coordinate gamma.

**Theorem 1.3 (The non-pole semicircle boundary attains zero).**

$$\forall delta \in \operatorname{Real}\left(\right), gamma \in \operatorname{Real}\left(\right), x \in \operatorname{Real}\left(\right), t \in \operatorname{Real}\left(\right),\; \left(\left(0 < delta \land \left(0 < x \land (x - delta)^{2} + (t - gamma)^{2} \ne 0\right)\right) \land (x)^{2} + (t - gamma)^{2} = (delta)^{2}\right) \Rightarrow activeSemicircleResponse\left(delta, gamma, x, t\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_boundary_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the bounding circle, away from the rational pole, the radial factor vanishes and the response is exactly zero. This supplies the equality case adjoining the strict negative interior.

**Theorem 1.4 (The two axis endpoints lie on the zero boundary).**

$$\forall delta \in \operatorname{Real}\left(\right), gamma \in \operatorname{Real}\left(\right),\; 0 < delta \Rightarrow \left(\left((0)^{2} + (gamma - delta - gamma)^{2} = (delta)^{2} \land activeSemicircleResponse\left(delta, gamma, 0, gamma - delta\right) = 0\right) \land \left((0)^{2} + (gamma + delta - gamma)^{2} = (delta)^{2} \land activeSemicircleResponse\left(delta, gamma, 0, gamma + delta\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_axis_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The circle meets the critical axis at gamma minus delta and gamma plus delta. Both points satisfy the circle equation and attain zero response.

**Theorem 1.5 (Left approach to the pole is unbounded below).**

$$\forall delta \in \operatorname{Real}\left(\right), gamma \in \operatorname{Real}\left(\right), B \in \operatorname{Real}\left(\right),\; 0 < delta \Rightarrow \left(\exists x \in \operatorname{Real}\left(\right),\; 0 < x \land \left(x < delta \land activeSemicircleResponse\left(delta, gamma, x, gamma\right) < B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_response_unbounded_near_pole` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real bound, an explicit point strictly between the critical axis and the pole has response below that bound. The construction uses x equals delta minus delta divided by n plus two.

**Theorem 1.6 (A bounded background cannot preserve nonnegativity).**

$$\forall delta \in \operatorname{Real}\left(\right), gamma \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right), B \in \operatorname{Real}\left(\right),\; \left(0 < delta \land \left(\forall u \in \operatorname{Real}\left(\right),\; \left(0 < u \land u < delta\right) \Rightarrow b\left(u\right) \le B\right)\right) \Rightarrow \left(\exists x \in \operatorname{Real}\left(\right),\; 0 < x \land \left(x < delta \land activeSemicircleResponse\left(delta, gamma, x, gamma\right) + b\left(x\right) < 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_bounded_background_loses_nonnegativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any additional contribution bounded above between the axis and the pole is dominated by the negative divergence. Thus the total response is strictly negative at some nearby point.

## References

- Truth anchor: `D5/S3/Analytic/Boundary/ActiveSemicircle.activeSemicircleResponse`
- Truth anchor: `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_axis_endpoints`
- Truth anchor: `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_boundary_zero`
- Truth anchor: `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_bounded_background_loses_nonnegativity`
- Truth anchor: `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_criterion`
- Truth anchor: `D5/S3/Analytic/Boundary/ActiveSemicircle.active_semicircle_response_unbounded_near_pole`
