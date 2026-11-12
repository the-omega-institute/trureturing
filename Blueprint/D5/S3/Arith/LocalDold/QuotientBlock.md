# The unitriangular block pairing

## Abstract

Actual quotient and normalized block ideal correspondence

This proves the integer ideal correspondence in the proof of manuscript Lemma 3.1. The quotient, remainder coefficients and impulse sequence are actual objects, with no equivalence supplied as a hypothesis. Nonconstant coordinates are listed in reverse order k-1,...,1; row j is the top-coefficient observation against x^j. Its matrix is lower triangular with diagonal one. The integer inverse therefore preserves the generated ideal. No nonzero trailing coefficient or irreducibility is required for this correspondence; scalar-return existence and exact p-adic lifting remain separate obligations. Source attribution and the full incomplete family are in `D5/L/Scale/jaidee2026blockdold`. Audit attempts and unfinished targets are disclosed under issue 29392.

**Theorem 1.1 (observation_ideal).**

Lean statement: `D5/S3/Arith/LocalDold/QuotientBlock.observation_ideal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/QuotientBlock.observation_ideal` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every integer recurrence of order k>=2 and every element q of its actual monic quotient, the k-1 values L(q*x^j), 0<=j<k-1, generate exactly the same ideal of Z as the nonconstant canonical-remainder coefficients of q. This is proved using the actual quotient power basis and a determinant-one pairing matrix, rather than assuming invertibility or block equality.

**Theorem 1.2 (block_coefficient_ideal).**

Lean statement: `D5/S3/Arith/LocalDold/QuotientBlock.block_coefficient_ideal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/QuotientBlock.block_coefficient_ideal` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every natural n, the actual impulse block U(n),...,U(n+k-2) and the nonconstant remainder coefficients of x^n generate the same integer ideal. The consumer applies observation_ideal to x^n and uses the previously checked identity L(x^m)=U(m). Integer divisibility by any modulus is consequently the same on both lists. The separate identification with scalar units at primes not dividing the trailing coefficient, rank existence, valuation lifting and positive-block hypotheses is not assumed or proved by this endpoint.

## References

- Truth anchor: `D5/S3/Arith/LocalDold/QuotientBlock.block_coefficient_ideal`
- Truth anchor: `D5/S3/Arith/LocalDold/QuotientBlock.observation_ideal`
- Dependency: [D5/S3/Arith/LocalDold/NormalizedQuotient](NormalizedQuotient.md)
