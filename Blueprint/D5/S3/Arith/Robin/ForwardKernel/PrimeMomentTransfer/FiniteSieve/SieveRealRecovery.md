# Sharp interval sieve moments at real scales

## Abstract

Sharp interval sieve moments at real scales

**Theorem 1.1 (Real-scale recovery of the sharp interval moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRealRecovery.finite_sieve_intervals`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRealRecovery.finite_sieve_intervals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Montgomery–Soundararajan Theorem 1 (MSFinite) and Kuperberg Theorem 1.3 specialised to the smoothed interval weights (KuperbergSmoothed). Then the finite-sieve interval third moment and fourth Wick defect estimates FiniteSieveIntervals, the conclusion of Lemma 498.3(c), hold: for every fixed M at least one, the sharp cubic sieve moments divided by (H log H) to the power three halves, and the sharp fourth Wick defects divided by H squared times log H squared, tend to zero uniformly over all ordered interval endpoints in [0,M], as real H tends to infinity. The modulus is exactly the primorial through the natural floor of ((M+5)H) to the power ten.

Set h to the natural floor of H and dilate every endpoint by H/h. The interval sums are unchanged, with the same modulus Q throughout. Eventually H is at most 2h and log H is at most 2 log h, so the integer estimates apply in the doubled window with doubled density constant. The scale (h log h) to the power k/2 is at most the corresponding real scale. Squarefreeness of the primorial and the existing density bound P(Q) at most B log H then give the result.

KuperbergSmoothed is the specialization of Kuperberg Theorem 1.3 to the real smoothed interval weights used here, expressed as finite-sieve expectations. It is an explicit hypothesis. Fourier admissibility of the smoothed weights and the Ramanujan coordinate identity are not proved here.

Together with MSSecond, interval_correlations_of_sieve_inputs gives IntervalCorrelations concreteSS.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRealRecovery.finite_sieve_intervals`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveIntegerRecovery](SieveIntegerRecovery.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SingularSeriesTail](SingularSeriesTail.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling](../RealLengthRescaling.md)
