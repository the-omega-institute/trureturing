# Sharp phase recovery for the synchronized native cubic clock

## Abstract

A five-prime decoder is optimal for the native synchronized cubic observations.

**Theorem 1.1 (Every positive native phase is recovered by five probes and no fewer).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicNativePhaseRecovery.native_phase_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicNativePhaseRecovery.native_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the base-field scalar cubic readout on the image of the integer Lucas recurrence. On the specified 21-prime alphabet, the observations live in a recurrent 24-phase clock with one exceptional first-level word.

The five readings at 5, 7, 47, 53 and 83 distinguish the first-level exception and recover every other level modulo 24. No four readings in that alphabet suffice; every separating set must read prime 47. The lower bound follows from a finite collision certificate and symbolic cardinality, not a prime-density argument. Replacing 53 by 109 recovers the common orientation without the separate calibrating probe 23.

The checked result concerns literal Lucas levels and operational cubic observations. Identification with a candidate's global tame conductor character, the candidate-prime Chebotarev density, and Wall-Sun-Sun are not conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicNativePhaseRecovery.native_phase_recovery`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Arith/Primes/GoldenCubicScalarFrobeniusReadout](GoldenCubicScalarFrobeniusReadout.md)
