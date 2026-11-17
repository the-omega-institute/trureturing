# Full interval correlations from finite sieve inputs

## Abstract

Full interval correlations from finite sieve inputs

**Theorem 1.1 (interval correlations of sieve inputs).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationAssembly.interval_correlations_of_sieve_inputs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationAssembly.interval_correlations_of_sieve_inputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assuming the Montgomery–Soundararajan square-sum asymptotic (MSSecond, a consequence of their Theorem 2 and equation (16)) and the finite-sieve interval third-moment and fourth Wick-defect conclusions (FiniteSieveIntervals, the conclusion of Lemma 498.3(c) for Q = primorial(floor(((M+5)H)^10))), the full singular series satisfies the interval correlation estimates (498.6)–(498.7). The primorial-family conclusion is assumed here; its derivation from Montgomery–Soundararajan Theorem 1 and Kuperberg Theorem 1.3 is not proved here. The second correlation has the overlap main term with error O(H); the third correlations, fourth Wick defects and fourth leading-term errors share one nonnegative error modulus, antitone on [2,infinity) and tending to zero. Combined with fixed_scale_third and fixed_scale_fourth, this yields §497’s (F₃)/(F₄) for ψ − id under HL₄(β), for 0 < θ < β < 1/4. Chinese-remainder moments and quantitative Euler tails provide part (b); the quadratic identities with coefficients P-2 and P-1 remove coincident indices in part (d).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationAssembly.interval_correlations_of_sieve_inputs`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCRTMoments](SieveCRTMoments.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCollisionRemoval](SieveCollisionRemoval.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCorrelationEnvelope](SieveCorrelationEnvelope.md)
