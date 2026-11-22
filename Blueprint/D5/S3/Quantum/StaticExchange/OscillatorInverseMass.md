# The inverse-mass criterion for finite equal-time fluctuations

## Abstract

A positive Euclidean oscillator tower has finite integrated spectral weight on positive frequencies exactly when its residues divided by their masses form a summable family.

**Definition 1.1 (One oscillator response).**

$$R(\omega)=\frac{a}{m^2+\omega^2}$$

*Formalization.* `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.oscillator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real pole weight is a and the mass is m.

**Definition 1.2 (Nonnegative oscillator tower).**

$$C(\omega)=\sum_{n} \max(0,\frac{a_n}{m_n^2+\omega^2})$$

*Formalization.* `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.tower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each real term is mapped into the extended nonnegative reals before summation. For nonnegative residues and positive masses this preserves every term, including cases where the series totals infinity.

**Theorem 1.3 (The positive-frequency integral of a single mode).**

$$0<m \Rightarrow R \in L^1(\mathbb{R}) \land \int_0^{\infty} R(\omega)\, d\omega=\frac{\pi}{2}\frac{a}{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.oscillator_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m>0 and any real weight a, the substitution u=ω/m reduces the integral to the arctangent integral π/2. The mode is absolutely integrable on the entire real line.

**Theorem 1.4 (Sharp finiteness criterion for a positive tower).**

$$\begin{aligned}&\forall n,a_n \ge 0 \land m_n>0\\&\Rightarrow \int_0^{\infty} C(\omega)\, d\omega=\sum_{n} \frac{\pi}{2}\frac{a_n}{m_n}\\&\land (\int_0^{\infty} C(\omega)\, d\omega<\infty \Leftrightarrow \sum_{n} \frac{a_n}{m_n}<\infty)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.tower_integral_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every mass is strictly positive and every residue is nonnegative. Tonelli's theorem integrates the countable nonnegative sum mode by mode, with infinite totals allowed. The constant π/2 is finite and positive, so the integrated response is finite exactly when the inverse-mass moment converges. The sequence may have repeated masses and arbitrarily small positive masses. With inverse Fourier measure dω/(2π), evenness makes the finite equal-time variance equal to the positive half-axis mass divided by π.

## References

- Truth anchor: `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.oscillator`
- Truth anchor: `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.oscillator_integral`
- Truth anchor: `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.tower`
- Truth anchor: `D5/S3/Quantum/StaticExchange/OscillatorInverseMass.tower_integral_criterion`
