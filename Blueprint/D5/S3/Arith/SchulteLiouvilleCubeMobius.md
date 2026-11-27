# Schulte's Liouville and Cube-Mobius Identity

## Abstract

Schulte's A299406 coefficients equal the Liouville function times A210826.

N denotes the natural numbers including zero, Z the integers, and ArithmeticFunction(Z) the integer-valued functions on N that vanish at zero. The indices n and k are natural numbers, and f is such an arithmetic function. The arithmetic function zeta is one on positive inputs and zero at zero; mu is the Mobius function; intCast(zeta) is its integer-valued cast, the coercion from ArithmeticFunction(N) to ArithmeticFunction(Z) that the convolutions with the integer-valued mu require. Omega counts prime factors with multiplicity, and lambda denotes Mathlib's liouville, A008836: at a positive index it is minus one raised to Omega of that index. A and B denote A299406 and A210826. The binary star is Dirichlet convolution, while the centered dot is integer multiplication of values. Nat.floorRoot divides each prime-factor exponent by k using natural-number division and returns zero when k or n is zero; it is the root for the divisibility order. The function liftPow keeps the value of f at this root exactly when its k-th power equals n. For positive k, its Dirichlet series is obtained by replacing the series variable s by k*s. Reading the Dirichlet generating function coefficientwise sends zeta(6s) to liftPow(6,zeta) and the reciprocals of zeta(2s) and zeta(3s) to liftPow(2,mu) and liftPow(3,mu). In the Lambert series, x is a formal variable: the sum of B(d) over positive divisors d of n equals the cube indicator, so Mobius inversion gives B as mu convolved with that indicator. Only the A299406 formula a(n) = A008836(n) * A210826(n) is asserted here, under these coefficient readings. Analytic convergence and other OEIS assertions are outside the claim. The positive-index hypothesis follows the offset one of A299406.

**Definition 1.1 (The exact power lift).**

$$\forall k \in \mathbb{N}, \forall f \in \operatorname{ArithmeticFunction}\left(\mathbb{Z}\right), \forall n \in \mathbb{N}, ((\operatorname{floorRoot}\left(k, n\right)^{k} = n) \implies (\operatorname{liftPow}\left(k, f\right)\left(n\right) = f\left(\operatorname{floorRoot}\left(k, n\right)\right))) \land ((\operatorname{floorRoot}\left(k, n\right)^{k} \neq n) \implies (\operatorname{liftPow}\left(k, f\right)\left(n\right) = 0))$$

*Formalization.* `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two defining clauses retain f at the factorization root on exact powers and give zero otherwise. They also describe the total definition when k is zero; the coefficient interpretation uses only positive k. Each displayed zero in a value equality is an integer.

**Definition 1.2 (The A299406 coefficient function).**

$$\operatorname{A} = ((\operatorname{intCast}\left(\operatorname{\zeta}\right) * \operatorname{liftPow}\left(6, \operatorname{intCast}\left(\operatorname{\zeta}\right)\right)) * \operatorname{liftPow}\left(2, \operatorname{\mu}\right)) * \operatorname{liftPow}\left(3, \operatorname{\mu}\right)$$

*Formalization.* `D5/S3/Arith/SchulteLiouvilleCubeMobius.A` (`✓ std3`).

*Citation.* Werner Schulte (2018). *OEIS A299406, coefficients of zeta(s) zeta(6s) / (zeta(2s) zeta(3s)), with the Liouville–A210826 product conjecture*. URL: <https://oeis.org/A299406>.

*Commentary.*

The four convolution factors encode zeta(s) zeta(6s) divided by zeta(2s) zeta(3s). The zeta factors here are integer-valued, matching the natural-to-integer coercions in the Lean definition.

**Definition 1.3 (The Lambert-series coefficient function).**

$$\operatorname{B} = \operatorname{\mu} * \operatorname{liftPow}\left(3, \operatorname{intCast}\left(\operatorname{\zeta}\right)\right)$$

*Formalization.* `D5/S3/Arith/SchulteLiouvilleCubeMobius.B` (`✓ std3`).

*Citation.* Werner Schulte (2018). *OEIS A299406, coefficients of zeta(s) zeta(6s) / (zeta(2s) zeta(3s)), with the Liouville–A210826 product conjecture*. URL: <https://oeis.org/A299406>.

*Commentary.*

The function liftPow(3,zeta) is one on positive cubes and zero elsewhere. Convolution with mu inverts the positive-divisor sum in the Lambert series defining A210826.

**Theorem 1.4 (Coefficients at exact powers).**

$$\forall k \in \mathbb{N},\; (k \ne 0) \implies (\forall f \in \operatorname{ArithmeticFunction}\left(\mathbb{Z}\right),\; \forall m \in \mathbb{N},\; \operatorname{liftPow}\left(k, f\right)\left(m^{k}\right) = f\left(m\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_apply_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an exact positive-degree power, the lift evaluates the original function at the base.

**Theorem 1.5 (Coefficients outside exact powers).**

$$\forall k \in \mathbb{N},\; \forall f \in \operatorname{ArithmeticFunction}\left(\mathbb{Z}\right),\; \forall n \in \mathbb{N},\; (Not (\exists m \in \mathbb{N},\; m^{k} = n)) \implies (\operatorname{liftPow}\left(k, f\right)\left(n\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_apply_nonpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the input has no natural k-th root, its coefficient in the lift is zero.

**Theorem 1.6 (Multiplicativity of the power lift).**

$$\forall k \in \mathbb{N},\; (k \ne 0) \implies (\forall f \in \operatorname{ArithmeticFunction}\left(\mathbb{Z}\right),\; (\operatorname{ArithmeticFunction}.\operatorname{IsMultiplicative}\left(f\right)) \implies (\operatorname{ArithmeticFunction}.\operatorname{IsMultiplicative}\left(\operatorname{liftPow}\left(k, f\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_isMultiplicative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coprime factors of an exact power are exact powers of the same degree.

**Theorem 1.7 (Power lift on prime powers).**

$$\forall k \in \mathbb{N},\; (k \ne 0) \implies (\forall f \in \operatorname{ArithmeticFunction}\left(\mathbb{Z}\right),\; \forall p \in \mathbb{N},\; \forall e \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies (\operatorname{liftPow}\left(k, f\right)\left(p^{e}\right) = (if (k \mid e) then f\left(p^{\operatorname{Nat}.\operatorname{div}\left(e, k\right)}\right) else 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent must be divisible by the lift degree. The quotient is natural-number division.

**Theorem 1.8 (Convolution on prime powers).**

$$\forall f \in \operatorname{ArithmeticFunction}\left(\mathbb{Z}\right),\; \forall g \in \operatorname{ArithmeticFunction}\left(\mathbb{Z}\right),\; \forall p \in \mathbb{N},\; \forall e \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((f * g)\left(p^{e}\right) = \operatorname{Finset}.\operatorname{sum}\left(\operatorname{Finset}.\operatorname{range}\left(e + 1\right), (fun i:\mathbb{N} \mapsto f\left(p^{i}\right) \cdot g\left(p^{e - i}\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.conv_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The divisors of p raised to e have exponents from zero to e. Their complementary exponents use natural subtraction.

**Theorem 1.9 (Lifted Möbius function on prime powers).**

$$\forall k \in \mathbb{N},\; (k \ne 0) \implies (\forall p \in \mathbb{N},\; \forall e \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies (\operatorname{liftPow}\left(k, \operatorname{\mu}\right)\left(p^{e}\right) = (if (e = 0) then 1 else 0) - (if (e = k) then 1 else 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.lift_moebius_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two integer indicators give one at exponent zero and minus one at exponent k.

**Theorem 1.10 (Lifted zeta on prime powers).**

$$\forall k \in \mathbb{N},\; (k \ne 0) \implies (\forall p \in \mathbb{N},\; \forall e \in \mathbb{N},\; (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies (\operatorname{liftPow}\left(k, \operatorname{ArithmeticFunction}.\operatorname{natCoe}\left(\operatorname{ArithmeticFunction}.\operatorname{zeta}\right)\right)\left(p^{e}\right) = (if (k \mid e) then 1 else 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.lift_zeta_prime_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer-valued lift gives one exactly when k divides the exponent.

**Theorem 1.11 (Schulte's product formula).**

$$\forall n \in \mathbb{N}, (0 < n) \implies (\operatorname{A}\left(n\right) = \operatorname{\lambda}\left(n\right) \cdot \operatorname{B}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchulteLiouvilleCubeMobius.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a299406-schulte-liouville-cube-mobius` (proved) by `D5/S3/Arith/SchulteLiouvilleCubeMobius.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a299406-schulte-liouville-cube-mobius","declaration_gid":"D5/S3/Arith/SchulteLiouvilleCubeMobius.result","resolution_kind":"proved"} -->

*Citation.* Werner Schulte (2018). *OEIS A299406, coefficients of zeta(s) zeta(6s) / (zeta(2s) zeta(3s)), with the Liouville–A210826 product conjecture*. URL: <https://oeis.org/A299406>.

*Commentary.*

Every convolution factor is multiplicative. On a prime power with exponent e, both sides have values 1, 1, 0, -1, -1, 0 as e runs through the six residue classes. Equality on all prime powers therefore gives equality at every positive natural index.

## References

- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.A`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.B`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.conv_prime_pow`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_apply_nonpow`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_apply_pow`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_isMultiplicative`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow_prime_pow`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.lift_moebius_prime_pow`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.lift_zeta_prime_pow`
- Truth anchor: `D5/S3/Arith/SchulteLiouvilleCubeMobius.result`
