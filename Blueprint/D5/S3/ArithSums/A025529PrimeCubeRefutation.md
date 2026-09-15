# A025529: a prime-cube counterexample

## Abstract

The prime cube 16843^3 refutes the composite-solution classification for A025529.

**Definition 1.1 (The LCM-weighted harmonic sum).**

$$\forall m \in \mathrm{Nat},\; \operatorname{A}\left(m\right) = \sum_{k = 1}^{m}\frac{\operatorname{lcmUpto}\left(m\right)}{k}$$

*Formalization.* `D5/S3/ArithSums/A025529PrimeCubeRefutation.A` (`✓ std3`).

*Citation.* Amiram Eldar; Thomas Ordowski; OEIS Foundation Inc. (2019). *OEIS A025529: the LCM-weighted harmonic sum and composite-solution conjecture*. URL: <https://oeis.org/A025529>.

*Commentary.*

Let L(m) be the least common multiple of 1 through m. Define A(m) as the sum of the exact natural quotients L(m)/k for 1<=k<=m. Under the rational embedding this is L(m) times harmonic(m), as proved inside the lifting argument. The conventions are L(0)=1, harmonic(0)=0 and A(0)=0.

**Definition 1.2 (The composite-solution predicate).**

$$PrimeSquareOnly \Leftrightarrow (\forall n \in \mathrm{Nat},\; ((1 < n) \land \left((\neg \operatorname{Prime}\left(n\right)) \land (n \mid \operatorname{A}\left(n - 1\right))\right)) \Rightarrow (\exists q \in \mathrm{Nat},\; (\operatorname{Prime}\left(q\right)) \land \left((3 < q) \land (n = q^{2})\right)))$$

*Formalization.* `D5/S3/ArithSums/A025529PrimeCubeRefutation.PrimeSquareOnly` (`✓ std3`).

*Citation.* Amiram Eldar; Thomas Ordowski; OEIS Foundation Inc. (2019). *OEIS A025529: the LCM-weighted harmonic sum and composite-solution conjecture*. URL: <https://oeis.org/A025529>.

*Commentary.*

PrimeSquareOnly is the formal encoding of the composite-solution conjecture in the 2019 comment on OEIS A025529: every composite n with n dividing A(n-1) is the square of a prime greater than three. The conjunction 1<n and not Prime(n) expresses compositeness.

**Theorem 1.3 (Lifting a short harmonic congruence).**

$$\forall p \in \mathrm{Nat},\; ((\operatorname{Prime}\left(p\right)) \land \left((3 < p) \land (\sum_{k = 1}^{p - 1}k^{-1} \bmod p^{3} = 0)\right)) \Rightarrow (p^{3} \mid \operatorname{A}\left(p^{3} - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A025529PrimeCubeRefutation.prime_cube_divides` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amiram Eldar; Thomas Ordowski; OEIS Foundation Inc. (2019). *OEIS A025529: the LCM-weighted harmonic sum and composite-solution conjecture*. URL: <https://oeis.org/A025529>.

*Commentary.*

For a prime p>3, work in the subring of rationals whose reduced denominators are not divisible by p. Write U(N) for the reciprocal sum over 1<=k<N with p not dividing k. Reflection k maps to N-k proves U(N)/N belongs to this subring whenever p divides N. Partitioning denominators gives p^2 H(p^3-1)=H(p-1)+p U(p^2)+p^2 U(p^3). The short ring congruence implies H(p-1)/p^3 belongs to the subring, by clearing the unit denominator (p-1)! abstractly. Since p^2 divides L(p^3-1), the rational identity for A transfers this to the asserted integer divisibility. The ring ZMod(p^3) is not treated as a field: every required denominator is proved to be a unit.

**Theorem 1.4 (The complete classification is false).**

$$\neg PrimeSquareOnly$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A025529PrimeCubeRefutation.prime_square_only_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amiram Eldar; Thomas Ordowski; OEIS Foundation Inc. (2019). *OEIS A025529: the LCM-weighted harmonic sum and composite-solution conjecture*. URL: <https://oeis.org/A025529>.

*Commentary.*

The proof establishes that 16843 is prime and checks all 16842 reciprocal terms modulo 16843^3, obtaining zero. The lifting theorem then proves 4778134229107 divides A(4778134229106). This integer equals 16843^3, is composite, and cannot equal the square of any prime. The finite computation occurs in the proof of the negation. Neither the trillion-term harmonic sum nor the large LCM is evaluated. No exact valuation-three assertion or all-exponent valuation identity is used.

## References

- Truth anchor: `D5/S3/ArithSums/A025529PrimeCubeRefutation.A`
- Truth anchor: `D5/S3/ArithSums/A025529PrimeCubeRefutation.PrimeSquareOnly`
- Truth anchor: `D5/S3/ArithSums/A025529PrimeCubeRefutation.prime_cube_divides`
- Truth anchor: `D5/S3/ArithSums/A025529PrimeCubeRefutation.prime_square_only_refuted`
