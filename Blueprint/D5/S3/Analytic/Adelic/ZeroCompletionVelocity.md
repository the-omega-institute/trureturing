# Zero Completion Velocity

## Abstract

A simple zero thread moves by the ratio of completion and spatial derivatives.

**Theorem 1.1 (The two partial derivatives determine zero motion).**

$$\forall F \in \operatorname{Real}\left(\right) \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right), rho \in \operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right), tau \in \operatorname{Real}\left(\right), dCompletion \in \operatorname{Complex}\left(\right), dSpatial \in \operatorname{Complex}\left(\right), v \in \operatorname{Complex}\left(\right),\; \left(\operatorname{HasFDerivAt}\left((p \mapsto F\left(\operatorname{fst}\left(p\right)\right)\left(\operatorname{snd}\left(p\right)\right)), \operatorname{smulRight}\left(\operatorname{fstCLM}\left(\operatorname{Prod}\left(\operatorname{Real}\left(\right), \operatorname{Complex}\left(\right)\right), \operatorname{Real}\left(\right)\right), dCompletion\right) + \operatorname{comp}\left(\operatorname{mulCLM}\left(dSpatial\right), \operatorname{sndCLM}\left(\operatorname{Prod}\left(\operatorname{Real}\left(\right), \operatorname{Complex}\left(\right)\right), \operatorname{Complex}\left(\right)\right)\right), \operatorname{pair}\left(tau, rho\left(tau\right)\right)\right) \land \left(\operatorname{HasDerivAt}\left(rho, v, tau\right) \land \left(\left(\forall u \in \operatorname{Real}\left(\right),\; F\left(u\right)\left(rho\left(u\right)\right) = 0\right) \land dSpatial \ne 0\right)\right)\right) \Rightarrow v = -\frac{dCompletion}{dSpatial}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ZeroCompletionVelocity.zero_completion_velocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bivariate Frechet derivative is displayed on the completion and spatial coordinate projections, so dCompletion and dSpatial are the two distinct partial derivatives of the same analytic object.

The named thread rho is differentiable with velocity v and remains in the zero locus at every completion parameter. Composing the joint derivative with that thread therefore gives zero total derivative.

Since the spatial coefficient is nonzero, cancellation solves the chain rule identity for v and yields the displayed quotient.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ZeroCompletionVelocity.zero_completion_velocity`
