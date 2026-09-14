# Exponent Divisibility for Vanishing Diagonals

## Abstract

Affine vanishing-diagonal exponents divide their own integer coefficients.

The note hanna2026a395833div quotes Hanna's A395833 generating equation and divisibility conjecture. Write a(p,n) for NegativePowerDiagonalModPrime.a(p,n), the coefficient of its unique normalized integer series A(p). The normalization is a(p,0)=a(p,1)=1, and for n>1 the coefficient of x^n in A(p)(x/A(p)(x)^((p-1)*(n-1)+1)) vanishes. The quotient uses the formal unit inverse. Thus slope d corresponds to p=d+1, and A395833 corresponds to p=3.

The parameters d and n are natural numbers. In the general formula, n-1 and the expression inside intCast are computed in the natural numbers; intCast is the embedding into the integers. In the A395833 formula, 2*intCast(n)-1 is integer arithmetic. Both divisibility conclusions are integer divisibility.

**Theorem 1.1 (Every positive slope).**

$$\forall d: \mathbb{N}, (1 \le d) \implies (\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{intCast}\left((d) \cdot (n - 1) + 1\right) \mid \operatorname{a}\left(d + 1, n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.exponent_self_divisibility` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a395833-diagonal-exponent-self-divisibility` (proved) by `D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.exponent_self_divisibility`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a395833-diagonal-exponent-self-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.exponent_self_divisibility","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Put e(n)=d*(n-1)+1. Expanding the vanishing diagonal expresses a(d+1,n) as the negative sum of a(d+1,m)*c for 1<=m<n, where c is the coefficient of degree n-m in A(d+1)^(-e(n)*m). The derivative coefficient identity gives e(n)*m dividing (n-m)*c. The affine difference e(m)=e(n)-d*(n-m) therefore gives e(n) dividing e(m)*c. Strong induction supplies e(m) dividing a(d+1,m), so every summand is divisible by e(n). The initial divisor e(1) is one.

**Theorem 1.2 (The A395833 divisibility conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (((2) \cdot (\operatorname{intCast}\left(n\right)) - 1) \mid \operatorname{a}\left(3, n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.hanna_conjecture_a395833` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2026). *OEIS A395833, divisibility by the vanishing-diagonal exponent*. URL: <https://oeis.org/A395833>.

*Commentary.*

Set d=2 in the general theorem. For n>=1 the exponent 2*(n-1)+1 equals 2*n-1, proving the quoted divisibility conjecture.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.exponent_self_divisibility`
- Truth anchor: `D5/S1/Recurrence/Residue/DiagonalExponentSelfDivisibility.hanna_conjecture_a395833`
- Dependency: [D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility](DiagonalVanishingIndexDivisibility.md)
