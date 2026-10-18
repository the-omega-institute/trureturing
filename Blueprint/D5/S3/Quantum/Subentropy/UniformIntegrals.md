# Uniform subentropy kernel integrals

## Abstract

Exact scalar integrals for the maximally mixed two- and four-level subentropy kernels.

All integrals use real Lebesgue measure on the open half-line t>0. The reciprocal difference is integrated as a single function; its separate reciprocal terms are not integrable.

**Theorem 1.1 (A convergent reciprocal difference).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \left(0 < a \land a \le b\right) \Rightarrow \left(\operatorname{IntegrableOn}\left(\lambda t:\mathbb{R}\mapsto\frac{1}{t + a} - \frac{1}{t + b}, \operatorname{Ioi}\left(0\right)\right) \land \int_{t > 0} \frac{1}{t + a} - \frac{1}{t + b} \mathrm{d} t = \operatorname{log}\left(b\right) - \operatorname{log}\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/UniformIntegrals.reciprocal_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and b with a≤b, log(t+a)−log(t+b) has nonnegative derivative 1/(t+a)−1/(t+b), tends to zero at infinity, and has endpoint value log a−log b. The fundamental theorem of calculus gives both integrability and the stated integral.

**Theorem 1.2 (Shifted inverse powers).**

$$\forall a \in \mathbb{R},\; 0 < a \Rightarrow \left(\forall n \in \mathbb{N},\; \operatorname{IntegrableOn}\left(\lambda t:\mathbb{R}\mapsto\frac{1}{\left(t + a\right)^{n + 2}}, \operatorname{Ioi}\left(0\right)\right) \land \int_{t > 0} \frac{1}{\left(t + a\right)^{n + 2}} \mathrm{d} t = \frac{1}{\left(n + 1\right) \cdot a^{n + 1}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/UniformIntegrals.inverse_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and a natural n, Mathlib integrableOn_add_rpow_Ioi_of_lt supplies integrability at exponent −n−2. Translation of Lebesgue measure and integral_Ioi_rpow_of_lt give the integral 1/((n+1)a^(n+1)).

**Theorem 1.3 (The two-level integral).**

$$\int_{t > 0} \frac{1}{t + \frac{1}{2}} - \frac{1}{t + 1} - \frac{1}{4 \cdot \left(t + \frac{1}{2}\right)^{2}} \mathrm{d} t = \operatorname{log}\left(2\right) - \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/UniformIntegrals.integral_uniformTwo_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antiderivative is log(t+1/2)−log(t+1)+(1/4)/(t+1/2). Its limit at infinity is zero and its value at zero is −log 2+1/2.

**Theorem 1.4 (The four-level integral).**

$$\int_{t > 0} \frac{1}{t + \frac{1}{4}} - \frac{1}{t + 1} - \frac{3}{8 \cdot \left(t + \frac{1}{4}\right)^{2}} + \frac{1}{16 \cdot \left(t + \frac{1}{4}\right)^{3}} - \frac{1}{256 \cdot \left(t + \frac{1}{4}\right)^{4}} \mathrm{d} t = \operatorname{log}\left(4\right) - \frac{13}{12}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/UniformIntegrals.integral_uniformFour_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The antiderivative is log(t+1/4)−log(t+1)+(3/8)/(t+1/4)−(1/32)/(t+1/4)^2+(1/768)/(t+1/4)^3. Its limit at infinity is zero and its value at zero is −log 4+13/12.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/UniformIntegrals.integral_uniformFour_kernel`
- Truth anchor: `D5/S3/Quantum/Subentropy/UniformIntegrals.integral_uniformTwo_kernel`
- Truth anchor: `D5/S3/Quantum/Subentropy/UniformIntegrals.inverse_power`
- Truth anchor: `D5/S3/Quantum/Subentropy/UniformIntegrals.reciprocal_difference`
