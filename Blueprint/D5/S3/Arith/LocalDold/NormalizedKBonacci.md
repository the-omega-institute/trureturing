# Normalized impulse k-bonacci arithmetic

## Abstract

Normalized impulse k-bonacci arithmetic

The actual natural sequence is constructed with Mathlib LinearRecurrence.mkSol and impulse initial values 0,...,0,1. It is distinct from the positive seeds 1,...,1,2 in KBonacciShifts. These general infinite proofs supply Proposition 7.1 arithmetic and the parity/rank and first-block parts of Theorem 7.2. Full exact 2-adic lifting, least local repair k+1, uniform affine sample and companion trace/graph/zeta identities remain unproved here. The exact formal generating function is checked by a transient application described below. No order 2-20 computation is substituted for these all-order results. The block_even_iff registration is declared_validated in the current scoped report. The other public targets remain unfinished under issue 29392.

Exact generating-function application: for every k>=2, the actual power series F=sum U(n)X^n satisfies (1-X-...-X^k)*F=X^(k-1). The transient checked application uses the same impulse constructor and actual recurrence, coefficient by coefficient, including the complete initial segment and every subsequent index. This is an infinite formal identity; no finite computation or analytic convergence is invoked, and no duplicate named theorem is delivered.

**Theorem 1.1 (difference).**

Lean statement: `D5/S3/Arith/LocalDold/NormalizedKBonacci.difference`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/NormalizedKBonacci.difference` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every positive order k and every m>=0, U(m+k+1)+U(m)=2U(m+k). The proof subtracts the two actual adjacent recurrence sums, without assuming the difference identity.

**Theorem 1.2 (term_parity).**

Lean statement: `D5/S3/Arith/LocalDold/NormalizedKBonacci.term_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/NormalizedKBonacci.term_parity` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every k>=2 and every n>=0, U(n) modulo two is zero precisely when n modulo k+1 is less than k-1, and is one otherwise. This is an infinite theorem, using the recurrence difference to prove the full parity period.

**Theorem 1.3 (block_even_iff).**

Lean statement: `D5/S3/Arith/LocalDold/NormalizedKBonacci.block_even_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/NormalizedKBonacci.block_even_iff` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every k>=2 and every n>=0, two divides the actual gcd of U(n),...,U(n+k-2) if and only if k+1 divides n. Thus the least positive mod-two block rank is k+1. This is a gcd theorem about the actual sequence, not a parameter called rank.

**Theorem 1.4 (positive_tail).**

Lean statement: `D5/S3/Arith/LocalDold/NormalizedKBonacci.positive_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/NormalizedKBonacci.positive_tail` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every k>=2, U(n)>0 at every n>=k-1. The proof uses strong induction and a genuinely positive summand of the actual recurrence.

**Theorem 1.5 (block_positive).**

Lean statement: `D5/S3/Arith/LocalDold/NormalizedKBonacci.block_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/NormalizedKBonacci.block_positive` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every k>=2 and every positive n, the actual k-1-term block gcd is strictly positive. Blocks before the positive tail contain the impulse value, and later blocks contain a positive term. Thus positive-index block valuations are finite.

**Theorem 1.6 (first_even_block).**

Lean statement: `D5/S3/Arith/LocalDold/NormalizedKBonacci.first_even_block`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LocalDold/NormalizedKBonacci.first_even_block` (`✓ std3`). ∎

*Citation.* Chatchawan Panraksa; Sawian Jaidee; Sompong Chuysurichay; Thomas Ward (2026). *Local Dold Congruences, Realizability, and Prime Densities for Linear Recurrence Sequences (supplied revised manuscript)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29392>.

*Commentary.*

For every k>=2, the actual block gcd at n=k+1 equals two. The proof derives U(k+t)=2^t throughout 0<=t<=k-1 and combines divisibility of the gcd into the first value two with the exact parity theorem.

## References

- Truth anchor: `D5/S3/Arith/LocalDold/NormalizedKBonacci.block_even_iff`
- Truth anchor: `D5/S3/Arith/LocalDold/NormalizedKBonacci.block_positive`
- Truth anchor: `D5/S3/Arith/LocalDold/NormalizedKBonacci.difference`
- Truth anchor: `D5/S3/Arith/LocalDold/NormalizedKBonacci.first_even_block`
- Truth anchor: `D5/S3/Arith/LocalDold/NormalizedKBonacci.positive_tail`
- Truth anchor: `D5/S3/Arith/LocalDold/NormalizedKBonacci.term_parity`
