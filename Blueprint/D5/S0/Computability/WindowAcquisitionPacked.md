# Original positive numeral acquisition

## Abstract

Original positive numeral acquisition.

The exact positive numeral is acquired from one legal input alone. The actual h counts all supplied windows; no separate height, number or word width enters the initial configuration. The empty window list with unit one is included.

One accepting execution retains the Horner column sum, padding-inclusive counter and exact numeral. The maximum coordinate starts at zero, grows by at most five times the previous maximum plus two, and is at most (five to the h minus one) divided by two. The numeral is strictly below the Fibonacci number at index 3h+3. Time and every historical-space charge belong to this same execution.

**Theorem 1.1 (original accepting packed resources).**

Lean statement: `D5/S0/Computability/WindowAcquisitionPacked.original_accepting_packed_resources`

*Proof.* Machine-checked in Lean as `D5/S0/Computability/WindowAcquisitionPacked.original_accepting_packed_resources` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: original_accepting_packed_resources : Function.Injective (finiteCode (α := Symbol)) ∧ ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ ∀ (w : List Window) (e : Bool), D5.S3.Arith.ZeckendorfFutureKernel.legal false (NativeContinuation.NullReplyFiber.highBits (w.map letter) ++ [e]) → 0 < numeral w e → ∃ T : ℕ, T ≤ A*(w.length+1)^2 ∧ run (initial w e) T = boundary (inputSource w e) w.length (finalColumns w e) 0 .done ∧ program (run (initial w e) T).control = .halt ∧ pair (finalColumns w e) = NativeContinuation.JointLaw.composition (w.map letter) ∧ valueCount (finalColumns w e) = w.length ∧ valueN (finalColumns w e) = numeral w e ∧ pair (finalColumns w e) = columnSum w ∧ maximumColumn [] = 0 ∧ (∀ b, maximumColumn (w ++ [b]) ≤ 5*maximumColumn w+2) ∧ 2*maximumColumn w+1 ≤ 5^w.length ∧ maximumColumn w ≤ (5^w.length-1)/2 ∧ valueN (finalColumns w e) < Nat.fib (3*w.length+3) ∧ (finalColumns w e).length ≤ 3*w.length+4 ∧ (∀ n ≤ T, chargedBits w e n ≤ B*(w.length+1)) ∧ (∀ n ≤ T, Frame (inputSource w e) w.length (3*w.length+5) (run (initial w e) n))

## References

- Truth anchor: `D5/S0/Computability/WindowAcquisitionPacked.original_accepting_packed_resources`
- Dependency: [D5/S0/Computability/WindowAcquisitionTerminal](WindowAcquisitionTerminal.md)
