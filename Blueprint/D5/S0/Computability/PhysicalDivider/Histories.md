# Framed Physical Division

## Abstract

One finite-control divider on sixteen sequential bit tapes supports arbitrary finite same-capacity call histories while preserving the caller's tapes and retained storage extents.

**Theorem 1.1 (Uniform calls with persistent physical storage).**

$$Tcall\le Cstep(Tdiv(w)+2)+301(w+1), Space\le F+K(w+1)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PhysicalDivider/Histories.framed_divider_histories` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The machine, its sixteen-tape family, finite control and positive constants are fixed before the width, operands, caller contents and number of calls. Fourteen tapes hold the divider stacks, operands, capacity, scratch and output. Two additional tapes hold arbitrary protected caller data. Every instruction performs one bit read, one bit write or one unit move on a selected active tape. Administrative transitions and return signalling use counted reads.

For width w at least one, the dividend satisfies 0 <= a < 2^w and the divisor satisfies 0 < d < 2^w. The capacity buffer has w bits. Old quotient and remainder buffers have lengths at most w and w+1, respectively. Active heads start at the parked boundary. The machine executes loading, reversal, padding, copying, division, output transfer, scratch clearing and parking. It returns fixedBits(w,a/d) and fixedBits(w+1,a%d), with the operand copies and protected caller tapes preserved. Scratch and obsolete active output have been cleared.

The source arithmetic time is Tdiv(w) = 2(w+1)+3+w(6(w+1)+10)+1. Cstep is the fixed sum of the bounded source-statement implementation budgets. The physical arithmetic proof uses the source divider's positive timed correctness theorem and controls stack growth separately within each short round. Preparation and return contribute a linear allowance. The coefficient 301 also pays the one-read reentry before a subsequent call.

F counts the protected tape intervals and their signed binary head descriptions. The remaining charge includes all active intervals, the encoded transition table, current finite control and signed binary active-head descriptions. Initial intervals include every encoded cell, including zero-valued cells and both bits of every delimiter. Every execution prefix retains all earlier charged intervals and contains earlier support and head positions. Erasure therefore cannot reduce the charged interval. The absolute positive K is independent of every operand and of the number of completed calls.

After any return, each next operand is supplied by an explicit sequence of writes and unit moves. A w-bit operand requires 6w+6 such actions. These two production costs are separate from the division time bound. This count covers writing already supplied bits; computing those bits in the surrounding executor has an additional, separate cost. Production preserves every other tape, returns the changed operand's head to the origin and retains all charged endpoints through every prefix. The following reentry read changes only control. Induction over an arbitrary finite list of valid operand pairs connects these exact returned boundaries without resetting the accumulated charge.

The result concerns this framed divider. It does not implement a six-codeword parser, a complete ML initializer or executor, an approximation transfer, or a quotient or hardware interpretation.

## References

- Truth anchor: `D5/S0/Computability/PhysicalDivider/Histories.framed_divider_histories`
