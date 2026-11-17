# The complete physical assertion is refuted

## Abstract

The primitive anchored numerator does not always admit a joint physical order

**Theorem 1.1 (Failure at r=5,s=2,u=3).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The claim quantifies over every r>=2, 0<s<r, coprime(r,s), and 0<u<r with su=1 in ZMod r. It asks for one physical permutation sigma and a literal fresh cut at most r, with both complete OriginalOrder assertions at the explicit numerator and its double. The refutation retains that full claim, including the original all-natural prefix predicates. At r=5,s=2,u=3 the explicit numerator is 20. All 120 original physical permutations and all six literal cuts are covered by the finite obstruction; the native centered sources at (5,20) and (6,40) are used directly.

The finite checks cover prefix lengths through 5 and 6. Any complete OriginalOrder would imply these finite checks, so their simultaneous impossibility refutes the original unbounded assertion. The proof expands Mathlib's original permutation recurrence and uses kernel decision reduction. It uses no native_decide, added axiom or copied narrow-orbit proof. NarrowDoublingOrbit retains its current arithmetic results. This finite refutation supplies no broader high-phase obstruction, complete Circle J result or official acceptance.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/NarrowChristoffelJointRefutation.result`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/NarrowDoublingOrbit](NarrowDoublingOrbit.md)
- Dependency: [D5/S3/Combinatorics/Circle/RunFirstEarTransport](../RunFirstEarTransport.md)
