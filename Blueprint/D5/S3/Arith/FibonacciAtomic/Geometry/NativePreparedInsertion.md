# Native prepared insertion

## Abstract

Native preparation and two-event insertion for the prepared restriction.

**Theorem 1.1 (Preparation on the actual guarded runner).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepares`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Alpha is the true-labelled native leaf and beta the false-labelled leaf. C is the ordered pair (beta,alpha). D(false) is (beta,C), D(true) is (C,beta), and M is ((C,alpha),alpha), with four leaves. For every natural k, preparation starts at alpha and reaches the repository right comb with k copies of C and tail M. It uses exactly 3*k+4 native calls. Each ordinary continuation executes promotion, root split, and left split; the terminal continuation adds a further left-left split. The run equation uses NativeGuardedLeafRepair.run, including its subtree guards and actual replacement, and context_run transports those same calls along the right spine.

**Theorem 1.2 (Every order of distinct insertion labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepared_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepared_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, every bit assignment on Fin k, and every duplicate-free list of labels, the fixed preparation followed by the flattened two-call insertions succeeds on the original native runner, with total call count 3*k+4+2*length(order). A zero bit promotes then splits the right leaf of C, through (beta,beta), ending at D(false). A one bit splits the left leaf then promotes the right leaf, through (C,alpha), ending at D(true). The addressed slot for zero-based label j is R repeated j times followed by L.

The exact endpoint is comb k B M, where B(j)=D(x(j)) for labels in the insertion list and B(j)=C otherwise. The proof transports each local successful trace through the actual native comb and changes only the designated slot. Duplicate-freeness therefore ensures the next slot is still C in every insertion order; guards are checked by the native execution rather than postulated.

This proves the source-relative preparation and literal insertion endpoint portion of Proposition 37.1. The unordered coloured quotient, active subset recognition, ordered labelled-bit decoding, current-term recorder reconstruction, update and scratch clearing, payload edit sums and induced peak equalities are separate obligations.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepared_insertion`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepares`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum](../FourExitRawEndpointSpectrum.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth](NativeFreshSensorGrowth.md)
