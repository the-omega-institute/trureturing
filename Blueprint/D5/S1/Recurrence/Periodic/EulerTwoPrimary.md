# The two-primary Euler component

## Abstract

Ordinary tangent coefficients have power-of-two divisors and secant coefficients are odd.

All indices and powers are natural. Parity projections S and T of the ordinary rational exponential series satisfy S prime equals S times T and T prime equals one plus T squared. The product invariant of U and U at negative X is proved using the existing rational linear ODE uniqueness supplier. Lucas congruence supplies evenness of the odd binomial terms.

**Theorem 1.1 (The tangent power-of-two bound).**

$$\forall s: \mathbb{N}, (2^{s} \mid \operatorname{E}\left(2 \cdot s + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerTwoPrimary.tangent_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction on s uses the tangent convolution; every odd binomial factor supplies the additional factor two. Zero is included.

**Theorem 1.2 (Secant coefficients are odd).**

$$\forall s: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{E}\left(2 \cdot s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerTwoPrimary.secant_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the secant convolution, all tangent coefficients except E(1) vanish modulo two. The surviving factor is odd.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/EulerTwoPrimary.secant_odd`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerTwoPrimary.tangent_power`
- Dependency: [D5/S1/Recurrence/Periodic/EulerUpDownSource](EulerUpDownSource.md)
- Dependency: [D5/S1/Recurrence/Residue/ParametricExponentialSquareCongruence](../Residue/ParametricExponentialSquareCongruence.md)
