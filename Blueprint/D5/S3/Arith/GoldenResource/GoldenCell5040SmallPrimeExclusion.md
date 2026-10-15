# Small Prime Exclusion For The 5040 Residue

## Abstract

The power residue excludes every additional prime below forty seven.

Let the natural index be divisible by 5040 and satisfy the power congruence with residue 2241. The earlier exponent-window theorem fixes the old primes two, three, five and seven. Here every prime strictly between seven and forty seven is excluded from the index. This is a statement about all indices satisfying the two hypotheses, with no bound on the index.

The proof first exposes the reusable kernel modEq_period_not_dvd: a period-one residue at a divisor contradicts a distinct target residue whenever the period divides the exponent. The 5040 theorem consumes this kernel for each explicit small-prime period.

**Theorem 1.1 (No residual prime below forty seven).**

$$\forall n, p \in \mathbb{N}, 5040 \mid n \land 3^{n} \equiv 2241 (\mathrm{mod} n) \land \operatorname{Prime}\left(p\right) \land 7 < p < 47 \implies \neg{p \mid n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenCell5040SmallPrimeExclusion.modEq_2241_small_prime_not_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The possible primes are eleven, thirteen, seventeen, nineteen, twenty three, twenty nine, thirty one, thirty seven, forty one and forty three. For all except twenty three, explicit periods 5, 3, 16, 18, 28, 30, 18, 8 and 42 respectively divide 5040. Raising a period-one congruence to the symbolic quotient forces residue one, contradicting the residue of 2241.

Twenty three needs a different argument. Three has eleventh power one modulo twenty three, so any power of three has eleventh power one there. The eleventh power of 2241 instead has residue twenty two. This case uses only the power congruence.

The scalar periods and residue contradictions are checked by Lean kernel computation; the exponent of the original index is handled symbolically. The result does not bound the number of residual prime factors, exclude forty seven, or prove the Robin inequality or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenCell5040SmallPrimeExclusion.modEq_2241_small_prime_not_dvd`
