# Real finite-sieve weights and smoothed interval assumptions

## Abstract

Real finite-sieve weights and smoothed interval assumptions

**Definition 1.1 (sieve weighted sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWeightedSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWeightedSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive modulus Q, real scale H and real weight f, the weighted sieve sum is the sum over natural shifts d of f(d/H) times the centered coprimality variable at d. The sum uses the finite-support summation convention.

**Definition 1.2 (sieve scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveScale`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a real scale H, the common normalization is the nonnegative square root of H log H.

**Definition 1.3 (sieve norm4).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveNorm4`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveNorm4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fourth norm of a real residue function is the fourth root of its fourth absolute moment under the uniform average modulo Q.

**Definition 1.4 (sieve uniform measure).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveUniformMeasure`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveUniformMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The uniform residue measure is counting measure on ZMod Q multiplied by the reciprocal of the positive modulus Q.

**Definition 1.5 (sieve product moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveProductMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveProductMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product moment of a finite family of real residue functions is the uniform expectation of their pointwise product.

**Definition 1.6 (sieve wick pairing).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWickPairing`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWickPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For four real residue functions, the Wick pairing is the sum of the three products of second moments associated with the three pair partitions.

**Definition 1.7 (sieve wick defect).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWickDefect`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWickDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For four real residue functions, the fourth Wick defect is their product moment minus their Wick pairing.

**Definition 1.8 (normalized interval sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.normalizedIntervalSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.normalizedIntervalSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized sharp interval sum is the centered sieve sum over the natural shifts in (aH,bH], divided by the square root of H log H.

**Definition 1.9 (normalized weighted sum).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.normalizedWeightedSum`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.normalizedWeightedSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized weighted sum is the weighted centered sieve sum divided by the square root of H log H.

**Definition 1.10 (msfinite).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.MSFinite`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.MSFinite` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Montgomery–Soundararajan Theorem 1 supplies the assumed scalar second-moment bound and fourth-moment Wick error. In the paper's normalisation, equations (11) and (15) give m_k = Q(φ(Q)/Q)^k V_k and E[(Σ Y_d)^k] = V_k, where the sum runs over 1 ≤ d ≤ n and Y_d is the centered coprimality variable used here; E is the uniform expectation modulo Q. Two nonnegative constants are independent of every positive modulus Q and natural length n at least one. Writing P=Q/φ(Q), the variance estimate in the proof of Theorem 1 (pp. 11–12) gives variance at most C2 n P, and the fourth-moment error is at most C4 n^(2-1/28) P^18.

**Definition 1.11 (sieve smoothing bump).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveSmoothingBump`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveSmoothingBump` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive delta, the real smooth bump is centered at twice delta, with inner radius delta/2 and outer radius delta.

**Definition 1.12 (smoothing kernel).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.smoothingKernel`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.smoothingKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive delta, the smoothing kernel is the real bump centered at twice delta, divided by its integral with respect to Lebesgue measure.

**Definition 1.13 (smoothed interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.smoothedInterval`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.smoothedInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive delta, the smoothed interval indicator at x is the integral of the smoothing kernel at r times the indicator of (a+r,b+r] at x.

**Definition 1.14 (kuperberg smoothed).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.KuperbergSmoothed`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.KuperbergSmoothed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assume Kuperberg Theorem 1.3 specialised to the fixed real smoothed interval indicators, in finite-sieve expectation coordinates. The assumed weighted identity is V_k(Q, h; f) = E ∏_i X_{f_i}, where f is the family of smoothed weights, X_{f_i} = sieveWeightedSum Q h f_i and E is the uniform expectation modulo Q; this identifies Kuperberg's weighted moments with the finite-sieve expectation. For each positive delta and each fixed ordered nonnegative endpoint family, nonnegative constants independent of squarefree Q and natural h at least three bound the cubic moment by C h^(3/2-1/21) P^(19/2) and the fourth Wick defect by C h^(2-1/28) P^18, respectively. Here P=Q/φ(Q). Fourier admissibility of the smoothed weights and the Ramanujan coordinate identity are not proved here.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.KuperbergSmoothed`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.MSFinite`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.normalizedIntervalSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.normalizedWeightedSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveNorm4`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveProductMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveScale`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveSmoothingBump`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveUniformMeasure`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWeightedSum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWickDefect`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.sieveWickPairing`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.smoothedInterval`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveAnalyticDefs.smoothingKernel`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/FiniteSieveDefs](FiniteSieveDefs.md)
