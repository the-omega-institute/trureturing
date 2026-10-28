# Complete prime-power envelope

## Abstract

The complete actual Mangoldt min envelope has an explicit uniform four-fifths bound.

**Theorem 1.1 (A four-fifths estimate with every prime power retained).**

Lean statement: `D5/S3/Weil/Mertens/CompleteMangoldtMinEnvelope.complete_mangoldt_min_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/CompleteMangoldtMinEnvelope.complete_mangoldt_min_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real L at least one, the actual series with coefficient Lambda(n)/sqrt(n) and factor min(1/L,n^(-5/2)) is summable, and its sum is at most (5/2)(log(4)+4)L^(-4/5). Lambda is the actual von Mangoldt function, so all prime powers remain in the series.

Abel summation is applied to the actual complete Chebyshev prefix psi(x). The head and tail are split at R=L^(2/5), and their psi(R) boundary terms cancel exactly. The existing unconditional estimate psi(x) <= (log(4)+4)x pays both remaining finite integrals. Uniform finite-prefix bounds establish both summability and the full sum bound without assuming an unproved tail limit.

This is the arithmetic envelope required by the simultaneous complex correlation bounds in the quadratic heat-loss refinement W372-W373. It supplies that complete arithmetic estimate only; it does not assert the analytic heat-filter identities, a numerical value for their other constants, positivity of the full signed zero pairing, the Riemann hypothesis, or strict Robin beyond 5040.

## References

- Truth anchor: `D5/S3/Weil/Mertens/CompleteMangoldtMinEnvelope.complete_mangoldt_min_envelope`
