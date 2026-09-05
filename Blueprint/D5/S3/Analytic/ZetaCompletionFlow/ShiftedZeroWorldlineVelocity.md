# Shifted-Zero Worldline Velocity

## Abstract

A shifted affine zero has a universal velocity and separates its horizontal label from its boundary-crossing time.

**Theorem 1.1 (The shifted zero moves with velocity minus i).**

$$\forall gamma \in \mathbb{R}, delta \in \mathbb{R}, omega \in \mathbb{R}, step \in \mathbb{R},\; \left(\neg step = 0\right) \Rightarrow \left(\left(\forall t \in \mathbb{R}, z \in \mathbb{C},\; \operatorname{shiftedObservation}\left(gamma, delta, t, z\right) = 0 \Leftrightarrow z = \operatorname{shiftedZeroWorldline}\left(gamma, delta, t\right)\right) \land \left(\frac{\operatorname{shiftedZeroWorldline}\left(gamma, delta, omega + step\right) - \operatorname{shiftedZeroWorldline}\left(gamma, delta, omega\right)}{step} = -i \land \left(\left(\forall t \in \mathbb{R},\; \operatorname{Re}\left(\operatorname{shiftedZeroWorldline}\left(gamma, delta, t\right)\right) = -gamma \land \operatorname{Im}\left(\operatorname{shiftedZeroWorldline}\left(gamma, delta, t\right)\right) = delta - t\right) \land \left(\forall t \in \mathbb{R},\; \operatorname{Im}\left(\operatorname{shiftedZeroWorldline}\left(gamma, delta, t\right)\right) = 0 \Leftrightarrow t = delta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaCompletionFlow/ShiftedZeroWorldlineVelocity.shifted_zero_worldline_universal_velocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every observation depth, the affine observation equation has exactly one root: the shifted-zero worldline with horizontal coordinate minus gamma and imaginary coordinate delta minus omega.

For every nonzero real step, the complex difference quotient is exactly minus i. The nonzero-step premise excludes the totalized-division degeneracy, while arbitrary gamma and delta make the velocity universal.

The imaginary coordinate vanishes exactly when the observation depth equals delta. Thus gamma records the horizontal label and delta records the boundary-crossing time; the theorem does not assert that the trajectory is a zero of the Riemann zeta function.

## References

- Truth anchor: `D5/S3/Analytic/ZetaCompletionFlow/ShiftedZeroWorldlineVelocity.shifted_zero_worldline_universal_velocity`
