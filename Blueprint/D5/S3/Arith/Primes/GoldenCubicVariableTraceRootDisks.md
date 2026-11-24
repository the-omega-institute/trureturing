# Variable golden trace and prime-power root disks

## Abstract

Identify the primitive signed traces and exact same-prime root disks of the golden block with variable starting seed.

**Theorem 1.1 (Primitive signed-trace roots and exact same-prime contact).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicVariableTraceRootDisks.actual_variable_trace_root_disks`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicVariableTraceRootDisks.actual_variable_trace_root_disks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterate the map x ↦ x³ + 3x from an arbitrary trace and add three to the square at the chosen level. At seed one, this is the protected golden Lucas block.

An integral companion product gives the square root needed for the primitive signed-trace parameter in the original field. This gives exact Frobenius returns for each actual root in characteristics other than two and three.

At every positive prime-power precision each residue root disk maps bijectively onto residues reducing to zero. Differences in the same root disk preserve divisibility by that same power of the prime.

This identifies the exact same-prime precision of changes to a starting seed in an actual root disk. The seed-one specialization is not a proof that the Wall–Sun–Sun divisibility case cannot occur.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicVariableTraceRootDisks.actual_variable_trace_root_disks`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
