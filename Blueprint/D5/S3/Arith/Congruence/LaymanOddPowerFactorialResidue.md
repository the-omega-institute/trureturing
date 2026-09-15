# Layman's Odd-Power Factorial Residue

## Abstract

Odd powers of a factorial have Layman's classified residue modulo the corresponding triangular number.

**Theorem 1.1 (Factorial divisibility outside the odd-prime branch).**

$$\forall n \in \mathrm{Nat},\; ((1 \le n) \land (\neg ((Prime\left(n + 1\right)) \land (Odd\left(n + 1\right))))) \Rightarrow ((n \cdot (n + 1)) / 2 \mid n!)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo P. Lava; Giorgio Balzarotti; John W. Layman (2010). *OEIS A119690, n! mod n*(n+1)/2*. URL: <https://oeis.org/A119690>.

*Commentary.*

For every natural n at least one, if n+1 is not an odd prime, then the triangular number n(n+1)/2 divides n!. This is a general-purpose reusable lemma with the residue theorem as its first consumer. In the even-n, odd-composite-successor case, a factorization n+1=a*b and parity give a+b<a*b, including when a=b. The embedding a!*b! divides (a+b)! and then n!, followed by coprime combination with n/2, proves the required divisibility.

**Theorem 1.2 (Layman's odd-power residue classification).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; 1 \le n \Rightarrow (n!^{2 \cdot k + 1} \bmod ((n \cdot (n + 1)) / 2) = (\operatorname{if} ((Prime\left(n + 1\right)) \land (Odd\left(n + 1\right))) \operatorname{then} n \operatorname{else} 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paolo P. Lava; Giorgio Balzarotti; John W. Layman (2010). *OEIS A119690, n! mod n*(n+1)/2*. URL: <https://oeis.org/A119690>.

*Commentary.*

For all natural n at least one and every natural k, the odd power (n!)^(2k+1) modulo n(n+1)/2 is n exactly in the odd-prime successor branch and is zero otherwise. In the prime branch, Wilson's theorem gives residue minus one modulo n+1, while factorial divisibility gives residue zero modulo n/2. Their coprime product combines these residues, and an odd power preserves both. The other branch uses the divisibility lemma.

## References

- Truth anchor: `D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime`
- Truth anchor: `D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.result`
