# Ferreira's odd-power residue radical identity

## Abstract

An odd-power residue sum determines the radical of its odd modulus.

The index n is natural. Remainders in the finite sum are the least nonnegative natural remainders. The radical is the product of distinct prime divisors. The deficit and quotient are rational.

**Definition 1.1 (The literal residue sum).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \sum_{k=1}^{4 \cdot n + 2} (k^{(4 \cdot n + 1)} \bmod (2 \cdot n + 1))$$

*Formalization.* `D5/S3/ArithSums/FerreiraOddPowerResidueRadical.a` (`✓ std3`).

*Citation.* Rui Ferreira (2026). *OEIS A399232, odd-power residue sum and radical identity*. URL: <https://raw.githubusercontent.com/oeis/oeisdata/2ce625d68f85e35e26e15c0d9681f69280c095e7/seq/A399/A399232.seq>.

*Commentary.*

Sum k to the power 4n+1 modulo 2n+1 over every integer k from one through 4n+2, including both complete blocks of residues.

**Theorem 1.2 (Positive deficit and radical quotient).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (0 < (2 \cdot n + 1)^{2} - \operatorname{a}\left(n\right)) \land \operatorname{rad}\left((2 \cdot n + 1)\right) = \frac{(2 \cdot n + 1)^{2}}{(2 \cdot n + 1)^{2} - \operatorname{a}\left(n\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/FerreiraOddPowerResidueRadical.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a399232-radical-identity` (proved) by `D5/S3/ArithSums/FerreiraOddPowerResidueRadical.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a399232-radical-identity","declaration_gid":"D5/S3/ArithSums/FerreiraOddPowerResidueRadical.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rui Ferreira (2026). *OEIS A399232, odd-power residue sum and radical identity*. URL: <https://raw.githubusercontent.com/oeis/oeisdata/2ce625d68f85e35e26e15c0d9681f69280c095e7/seq/A399/A399232.seq>.

*Commentary.*

Set m=2n+1 and r=rad(m). Divisibility of x to the power 4n+1 by m is equivalent to divisibility of x by r. Thus exactly m/r members of a complete block have zero remainder. Negation pairs each nonzero remainder with its complement in m. The two literal blocks therefore satisfy a(n)+m(m/r)=m squared. The signed rational deficit is m(m/r)>0, and r(m/r)=m gives the quotient.

## References

- Truth anchor: `D5/S3/ArithSums/FerreiraOddPowerResidueRadical.a`
- Truth anchor: `D5/S3/ArithSums/FerreiraOddPowerResidueRadical.result`
