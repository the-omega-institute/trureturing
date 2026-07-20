# Golden Norm

## Abstract

The golden norm is multiplicative and agrees with the scaled mathlib norm.

`D5/S0/Carrier/Norm` defines `N(a+b*phi)=a^2+ab-b^2`. Multiplying an element by its conjugate eliminates the `phi` coordinate and produces this integer, which makes the multiplicativity proof a direct polynomial identity.

Under the doubled `Zsqrtd 5` coordinates from the carrier module, the mathlib norm is exactly four times the golden norm. This factor is the expected square of the coordinate scaling.

**Remark 1.1 (The two-square norm as a shared interpretive core).**

$$
\operatorname{gaussianNorm}\left(a, b\right) = a^{2} + b^{2}
$$

*Source.* Repository-derived.

*Commentary.*

The source groups a^2+b^2 under four roles: the defining two-axis norm, the Gaussian norm, the modulus-four obstruction, and the splitting reading modulo a prime. It states that each role has its own theorem and that norm multiplicativity is the pivot used in the composition step. The vocabulary in which primes congruent to one split, primes congruent to three remain inert, and two ramifies is explicitly interpretive: the classification theorem is said not to depend on that Gaussian-integer language. A separate dynamical role is referenced but not added as a claim of this module.
