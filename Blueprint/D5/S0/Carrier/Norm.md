# Golden Norm

## Abstract

The golden norm is multiplicative and agrees with the scaled mathlib norm.

`D5/S0/Carrier/Norm` defines `N(a+b*phi)=a^2+ab-b^2`. Multiplying an element by its conjugate eliminates the `phi` coordinate and produces this integer, which makes the multiplicativity proof a direct polynomial identity.

Under the doubled `Zsqrtd 5` coordinates from the carrier module, the mathlib norm is exactly four times the golden norm. This factor is the expected square of the coordinate scaling.

**Theorem 1.1 (Norm of a natural power).**

$$\forall x\in\mathbb{Z}[\varphi],\ \forall n\in\mathbb{N},\ N(x^n)=N(x)^n$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/NormPowers.norm_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing norm is packaged as a monoid homomorphism from `GoldenInt` to `Int`. Applying its standard power law gives the exact identity for every golden integer and every natural exponent, with no extra algebraic assumptions.

**Remark 1.2 (The two-square norm as a shared interpretive core).**

$$
\operatorname{gaussianNorm}\left(a, b\right) = a^{2} + b^{2}
$$

*Source.* Repository-derived.

*Commentary.*

The source groups a^2+b^2 under four roles: the defining two-axis norm, the Gaussian norm, the modulus-four obstruction, and the splitting reading modulo a prime. It states that each role has its own theorem and that norm multiplicativity is the pivot used in the composition step. The vocabulary in which primes congruent to one split, primes congruent to three remain inert, and two ramifies is explicitly interpretive: the classification theorem is said not to depend on that Gaussian-integer language. A separate dynamical role is referenced but not added as a claim of this module.

**Theorem 1.3 (Norm-Euclidean division).**

$$\forall a,b\in\mathbb{Z}[\varphi],\ b\neq 0 \Rightarrow \exists q,r\in\mathbb{Z}[\varphi],\ a=qb+r \land (r=0 \lor \lvert\operatorname{norm}(r)\rvert<\lvert\operatorname{norm}(b)\rvert)$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/Euclidean.golden_division` (`✓ std3`). ∎

*Citation.* H. Chatland (1949). *On the Euclidean algorithm in quadratic number fields*. DOI: [10.1090/S0002-9904-1949-09315-1](https://doi.org/10.1090/S0002-9904-1949-09315-1).

*Commentary.*

For `a` and nonzero `b`, divide `a * conj(b)` by the nonzero integer `N(b)` and round both rational coordinates in the integral basis `(1, phi)`. Mathlib's nearest-integer operation makes the tie rule deterministic.

If the two coordinate errors are `x` and `y`, then each has absolute value at most `1/2`. Completing squares bounds `|x^2 + xy - y^2|` by `5/16`, so multiplicativity of the norm gives a remainder with strictly smaller absolute norm.

The `EuclideanDomain GoldenInt` instance uses this quotient and remainder with Euclidean relation `(N(r)).natAbs < (N(b)).natAbs`.
