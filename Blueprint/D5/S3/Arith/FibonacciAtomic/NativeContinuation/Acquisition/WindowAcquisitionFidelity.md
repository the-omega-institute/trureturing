# Read-only input and exact returned frame

## Abstract

Read-only input and exact returned frame.

The input tape is read-only at every time, including after the program halts. At the canonical endpoint its head is at the actual independent unit position. All work heads are at origin. The original packed column stays unchanged.

Unused tracks remain blank. Each normalized register has at most one more bit than the packed column length. The separate registers are a stronger endpoint for arithmetic continuation; a routine requiring another tape convention or a parked input head needs a paid connecting run.

**Theorem 1.1 (run source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.run_source`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.run_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: run_source (c : Config) (n : ℕ) : (run c n).cell sourceTrack=c.cell sourceTrack

**Theorem 1.2 (endpoint frame).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.endpoint_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.endpoint_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: endpoint_frame (w : List Window) (e : Bool) : (registerEnd w e).cell sourceTrack=inputSource w e ∧ (registerEnd w e).cell workTrack=word (Original.finalColumns w e) ∧ (∀ t : Track,(∀ j : Lane,t ≠ target j) → t ≠ sourceTrack → t ≠ workTrack → (registerEnd w e).cell t=fun _=>.blank) ∧ (∀ t : Track,(registerEnd w e).head t=if t=sourceTrack then w.length else 0) ∧ (∀ j : Lane,(normalized ((Original.finalColumns w e).map (select j))).length ≤ (Original.finalColumns w e).length+1)

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.endpoint_frame`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowAcquisitionFidelity.run_source`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalAcquisition](WindowCanonicalAcquisition.md)
