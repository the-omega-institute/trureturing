# Dale's A112041 Prime-Scaling Conjecture

## Abstract

Four prime values at successive powers-of-three scalings force k to be four or divisible by ten.

**Definition 1.1 (Dale's divisibility conjecture).**

$$\forall k \in {\mathbb N},\; (k > 0) \Rightarrow ((((\operatorname{Prime}\left(k + 1\right)) \land ((\operatorname{Prime}\left(3 \cdot k + 1\right)) \land ((\operatorname{Prime}\left(9 \cdot k + 1\right)) \land (\operatorname{Prime}\left(27 \cdot k + 1\right)))))) \Rightarrow (((k = 4) \lor (10 \mid k))))$$

*Formalization.* `D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.claim` (`✓ std3`).

*Citation.* Pierre Cami; Harvey P. Dale (2015). *OEIS A112041, Numbers k such that 1*k + 1, 3*k + 1, 9*k + 1, 27*k + 1 are all primes*. URL: <https://oeis.org/A112041>.

*Commentary.*

For every positive natural k, if k+1, 3k+1, 9k+1, and 27k+1 are all prime, then k is four or divisible by ten.

**Theorem 1.2 (The prime-scaling theorem).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a112041-dale-triple-scaling-prime-multiples-of-ten` (proved) by `D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a112041-dale-triple-scaling-prime-multiples-of-ten","declaration_gid":"D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pierre Cami; Harvey P. Dale (2015). *OEIS A112041, Numbers k such that 1*k + 1, 3*k + 1, 9*k + 1, 27*k + 1 are all primes*. URL: <https://oeis.org/A112041>.

*Commentary.*

Parity first forces k to be even: an odd k would make the prime k+1 equal to two, after which 3k+1 is composite. A split into residue classes modulo five then makes one of 9k+1, 27k+1, or 3k+1 a proper multiple of five, except when k is congruent to four and the prime k+1 equals five. The remaining residue class is divisible by both two and five.

## References

- Truth anchor: `D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.claim`
- Truth anchor: `D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.result`
