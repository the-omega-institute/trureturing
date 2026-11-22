# Recovering an isotropic shell density from one coordinate

## Abstract

The uniform coordinate kernel of a positive-radius shell gives a density transform. If the shell density is continuous and its projection tails are absolutely integrable, differentiation recovers it at every positive radius.

**Definition 1.1 (Coordinate density of a shell mixture).**

$$P(t)=\int_{t}^{\infty} \frac{h(r)}{2r}\, dr$$

*Formalization.* `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For t≥0, mix the uniform coordinate density on (−r,r) against the radius density h(r). The lower limit t restricts the integral to shells reaching that coordinate.

**Definition 1.2 (Shell density from a derivative).**

$$h(r)=-2rd(r)$$

*Formalization.* `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.shell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here d is the derivative of the coordinate density at positive radii. The reconstructed density at zero equals zero for every choice of d(0).

**Theorem 1.3 (Projection and mass of the reconstructed density).**

$$\begin{aligned}&\forall r \ge 0,h(r) \ge 0\\&\forall t \ge 0,P(t)=f(t)\\&\int_{0}^{\infty} h(r)\, dr=2\int_{0}^{\infty} f(r)\, dr\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.shell_projection_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume f is right-continuous at zero and absolutely integrable on the positive half-line, with derivative d(r)≤0 at every positive radius. Monotonicity bounds r f(r) by integrals of |f| on tails and yields its decay. Applying the improper fundamental theorem to r f(r) minus an antiderivative of f gives absolute integrability of r d(r). For h(r)=−2r d(r), the tail integrand is −d(r) for r>0. Integrating the derivative recovers f(t), and integration by parts against r gives the total mass of the even extension of f.

**Theorem 1.4 (Pointwise recovery on positive radii).**

$$\forall r>0,h(r)=-2rf'(r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.shell_density_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume h is continuous on positive radii, h(r)/(2r) is absolutely integrable on every positive tail, and its tail integral equals f(t) at every t>0. Subtracting two tails gives the integral on their intervening interval. The fundamental theorem of calculus then gives f′(r)=−h(r)/(2r) at every positive r.

## References

- Truth anchor: `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.projection`
- Truth anchor: `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.shell`
- Truth anchor: `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.shell_density_unique`
- Truth anchor: `D5/S3/Quantum/StaticExchange/IsotropicShellInversion.shell_projection_mass`
