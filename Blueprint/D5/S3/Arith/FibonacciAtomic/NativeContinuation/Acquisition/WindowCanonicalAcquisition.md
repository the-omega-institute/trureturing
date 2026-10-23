# Exact canonical acquisition from legal window words

## Abstract

Exact canonical acquisition from legal window words.

A single fixed eight-track finite-alphabet program precedes all legal five-window words and independent terminal units with positive original numeral. It reads the actual word, constructs the Horner column and actual height, completes the numeral, and physically produces four canonical registers.

The packed and canonical phases share one attained execution. Time is bounded by an absolute constant times the square of h+1, and the total persistent charge at every prefix by another absolute constant times h+1. The original Horner composition, column sum, growth recurrence and strict Fibonacci capacity are retained. These claims concern input acquisition; three dependent function calls and six output rows require further execution.

**Theorem 1.1 (original canonical acquisition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalAcquisition.original_canonical_acquisition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalAcquisition.original_canonical_acquisition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: original_canonical_acquisition : Function.Injective (finiteCode (α := Symbol)) ∧ ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ ∀ (w : List Window) (e : Bool), D5.S3.Arith.ZeckendorfFutureKernel.legal false (NativeContinuation.NullReplyFiber.highBits (w.map Original.letter) ++ [e]) → 0 < Original.numeral w e → ∃ T : ℕ, T ≤ A*(w.length+1)^2 ∧ run (initial w e) T = registerEnd w e ∧ program (registerEnd w e).control = .halt ∧ RegisterRep (registerEnd w e) 0 (value1 (Original.finalColumns w e)) ∧ RegisterRep (registerEnd w e) 1 (value2 (Original.finalColumns w e)) ∧ RegisterRep (registerEnd w e) 2 w.length ∧ RegisterRep (registerEnd w e) 3 (Original.numeral w e) ∧ Original.pair (Original.finalColumns w e) = NativeContinuation.JointLaw.composition (w.map Original.letter) ∧ Original.pair (Original.finalColumns w e) = Original.columnSum w ∧ Original.maximumColumn [] = 0 ∧ (∀ b, Original.maximumColumn (w ++ [b]) ≤ 5*Original.maximumColumn w+2) ∧ 2*Original.maximumColumn w+1 ≤ 5^w.length ∧ Original.maximumColumn w ≤ (5^w.length-1)/2 ∧ Original.numeral w e < Nat.fib (3*w.length+3) ∧ (∀ n ≤ T, charged w e n ≤ B*(w.length+1)) ∧ (∀ n ≤ T, ∀ t, 0 ≤ (run (initial w e) n).head t ∧ (run (initial w e) n).head t ≤ 3*w.length+6)

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowCanonicalAcquisition.original_canonical_acquisition`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterResources](WindowRegisterResources.md)
