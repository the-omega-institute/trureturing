# Full profinite adding machine of cubic Lucas blocks

## Abstract

The native cubic Lucas orbit realizes the full profinite adding machine.

**Theorem 1.1 (The actual omega-limit is homeomorphic to the profinite integers).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full positive-modulus time labels, with the product topology, parameterize the simultaneous residue limits of the actual native Lucas trajectory, bijectively and continuously in both directions.

**Theorem 1.2 (The cubic step is addition by one).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine_next`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Advancing the profinite time by one is exactly the native cubic update followed by reduction at every observation coordinate.

**Theorem 1.3 (Every actual forward reading is isolated in the full closure).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.actualReading_open`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.actualReading_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One three-adic cylinder separates an actual reading from every different point of the full closure. All omega-limit tuples nevertheless have ternary coordinate one.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.actualReading_open`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine_next`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicProfiniteClock](GoldenCubicProfiniteClock.md)
- Dependency: [D5/S3/Arith/Primes/ProfiniteObservationTopology](ProfiniteObservationTopology.md)
