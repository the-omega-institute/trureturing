# Pillai mean and shared kernels

## Abstract

The classical Pillai mean and elementary kernels used by the full A400361 proof.

P(n) is the original Pillai gcd sum. The second-order Pillai asymptotic is classical mathematics and is not a separate open-problem resolution. The full A400361 proof consumes this mean and the elementary finite-sum and limit kernels below.

**Definition 1.1 (The real restriction of zeta).**

$$\forall x \in \operatorname{Real}\left(\right), \operatorname{zetaR}\left(x\right) = \operatorname{re}\left(\operatorname{zeta}\left(\operatorname{ofReal}\left(x\right)\right)\right)$$

*Formalization.* `D5/S3/ArithSums/A400361PillaiMean.realZeta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

For every real x, zetaR(x) is the real part of complex zeta at x. Its real derivative at two equals the real part of the complex derivative; the proof uses differentiability at two.

**Theorem 1.2 (The telescoping kernel prefix).**

$$\forall N \in \operatorname{Nat}\left(\right), \sum_{j \in \operatorname{range}\left(N\right)} {\frac{1}{\left(j + 1\right) \cdot \left(j + 2\right)}} = 1 - \frac{1}{N + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A400361PillaiMean.kernel_one_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

For every natural N, the sum from j=0 to N-1 of 1/((j+1)*(j+2)) is 1-1/(N+1), including the empty prefix. It is the reciprocal specialization of Mathlib's Finset.sum_range_sub'. This identity is consumed by the kernel sum and reciprocal-square tail.

**Theorem 1.3 (The telescoping kernel series).**

$$\operatorname{HasSum}\left(j \mapsto \frac{1}{\left(j + 1\right) \cdot \left(j + 2\right)}, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A400361PillaiMean.hasSum_kernel_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

The index j ranges over all natural numbers. The nonnegative kernel series sums to one. It supplies both the d=1 digamma boundary and the reciprocal-square tail estimate.

**Theorem 1.4 (The triangular sum).**

$$\forall q \in \operatorname{Nat}\left(\right), \sum_{r \in \operatorname{Icc}\left(1, q\right)} {\operatorname{toReal}\left(r\right)} = \frac{\operatorname{toReal}\left(q\right) \cdot \left(\operatorname{toReal}\left(q\right) + 1\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A400361PillaiMean.sum_Icc_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

Every positive integer through q is included. The equality is in the reals and holds also at q=0. It follows from Mathlib's Finset.sum_range_id_mul_two by casting and changing the summation interval.

**Theorem 1.5 (The quotient ratio limit).**

$$\forall d \in \operatorname{Nat}\left(\right), \operatorname{TendstoAtTop}\left(N \mapsto \frac{\operatorname{toReal}\left(\operatorname{natDiv}\left(N, d\right)\right)}{\operatorname{toReal}\left(N\right)}, \frac{1}{\operatorname{toReal}\left(d\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A400361PillaiMean.quotient_ratio_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

N tends to infinity through all natural numbers. The parameter d is any natural number, including zero: natural division and real inversion both use their total zero conventions there. Positive parameters give the usual floor quotient ratio.

**Theorem 1.6 (The classical second-order Pillai mean).**

$$\operatorname{TendstoAtTop}\left(N \mapsto \frac{\sum_{n \in \operatorname{Icc}\left(1, N\right)} {\operatorname{toReal}\left(\operatorname{P}\left(n\right)\right)}}{\operatorname{toReal}\left(N\right)^{2}} - \frac{3}{pi^{2}} \cdot \operatorname{log}\left(N\right), \frac{3}{pi^{2}} \cdot \left(\frac{-1}{2} + 2 \cdot gamma - \frac{6 \cdot \operatorname{derivZetaR}\left(2\right)}{pi^{2}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A400361PillaiMean.pillai_second_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka; OEIS Foundation Inc. (2026). *OEIS A400361 revision 17, the second-order Pillai minus floor-gcd conjecture*. URL: <https://oeis.org/A400361>.

*Commentary.*

The exact weighted divisor-pair hyperbola identity at floor(sqrt(N)) and the harmonic-number limit give W(N)/N^2-log(N)/2 -> gamma-1/4. The original Pillai divisor formula yields its Mobius convolution. Dominated convergence and explicit quotient-square and tail estimates transfer the full second term without restricting N. The actual zeta-Mobius Dirichlet identity and its derivative at two evaluate the two Mobius moments, supplying the literal zeta derivative. This result is consumed by the complete A400361 theorem.

## References

- Truth anchor: `D5/S3/ArithSums/A400361PillaiMean.hasSum_kernel_one`
- Truth anchor: `D5/S3/ArithSums/A400361PillaiMean.kernel_one_prefix`
- Truth anchor: `D5/S3/ArithSums/A400361PillaiMean.pillai_second_term`
- Truth anchor: `D5/S3/ArithSums/A400361PillaiMean.quotient_ratio_limit`
- Truth anchor: `D5/S3/ArithSums/A400361PillaiMean.realZeta`
- Truth anchor: `D5/S3/ArithSums/A400361PillaiMean.sum_Icc_cast`
- Dependency: [D5/S3/Factorization/AlternatingGcdSumPillai](../Factorization/AlternatingGcdSumPillai.md)
