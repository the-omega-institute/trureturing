# One fixed acquisition and handoff program

## Abstract

One fixed acquisition and handoff program.

The finite control is the disjoint union of the packed acquisition control and the four-register control. The first actual packed completion enters register transfer after a paid read. All instructions remain local finite-symbol actions.

The first completion agrees with the packed run at every earlier prefix. Extending the program changes no earlier source acquisition state. Fixed code length and finite control do not depend on the supplied number or height.

**Theorem 1.1 (first done lift).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterProgram.first_done_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterProgram.first_done_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: first_done_lift (c : Configuration) (T : ℕ) (hc : (PhysicalWindowContinuation.run c T).control=.done) : ∃ s≤T,run (base c) s=base (PhysicalWindowContinuation.run c T) ∧ ∀ n ≤ s, run (base c) n=base (PhysicalWindowContinuation.run c n)

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterProgram.first_done_lift`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterComposition](WindowRegisterComposition.md)
