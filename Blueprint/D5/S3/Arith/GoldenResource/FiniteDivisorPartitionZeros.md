# Zeros of finite divisor partition functions

## Abstract

Finite divisor partition functions have explicit local zeros and no zeros off the imaginary axis.

**Definition 1.1 (A finite geometric factor).**

$$\operatorname{localFactor}\left(p, a, s\right) = \sum_{j=0}^{a} {{p}^{-s}}^{j}$$

*Formalization.* `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.localFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural base p and exponent a, sum the powers of p to minus s from degree zero through degree a. The exponent a may be zero.

**Definition 1.2 (The finite divisor partition function).**

$$\operatorname{partition}\left(N, s\right) = \prod_{p \mid N, \operatorname{Prime}\left(p\right)} \operatorname{localFactor}\left(p, \operatorname{factorization}\left(N, p\right), s\right)$$

*Formalization.* `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive integer N, multiply the local factors over its distinct prime divisors. The exponent in each factor is that prime's multiplicity in N. For N equal to one the empty product is one.

**Theorem 1.3 (The exact local zero lattice).**

$$\operatorname{localFactor}\left(p, a, s\right) = 0 \iff \exists k \in \mathbb{Z}, s = \frac{2 \pi i k}{(a+1) \log p} \land \neg(a+1 \mid k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.local_factor_eq_zero_iff` (`✓ std3`). ∎

*Citation.* Mathlib contributors (2026). *Finite geometric sums and complex exponential roots in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Field/GeomSum.lean>.

*Commentary.*

Let p be prime and a a natural number. A zero has the form two pi i k divided by (a+1) log p, where k is an integer not divisible by a+1. The finite geometric sum vanishes precisely when its ratio has (a+1)-st power one but is not one. Solving the exponential equation gives the lattice; excluding ratio one removes exactly the divisible indices. When a is zero, there are no such indices.

**Theorem 1.4 (A local zero has real part zero).**

$$\operatorname{localFactor}\left(p, a, s\right) = 0 \Rightarrow \Re s = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.local_factor_zero_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A root of unity has modulus one. The modulus of p to minus s is p to minus the real part of s. Since a prime p is greater than one, injectivity of the real exponential forces the real part to be zero.

**Theorem 1.5 (Nonvanishing away from the imaginary axis).**

$$\Re s \neq 0 \Rightarrow \operatorname{partition}\left(N, s\right) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.partition_ne_zero_of_re_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the real part of s is nonzero, every local factor is nonzero. A finite product of nonzero complex numbers is nonzero.

**Theorem 1.6 (Every zero lies on the imaginary axis).**

$$\operatorname{partition}\left(N, s\right) = 0 \Rightarrow \Re s = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.partition_zero_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the nonvanishing statement contrapositively to the same finite divisor partition function.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.localFactor`
- Truth anchor: `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.local_factor_eq_zero_iff`
- Truth anchor: `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.local_factor_zero_re`
- Truth anchor: `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.partition`
- Truth anchor: `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.partition_ne_zero_of_re_ne_zero`
- Truth anchor: `D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros.partition_zero_re`
