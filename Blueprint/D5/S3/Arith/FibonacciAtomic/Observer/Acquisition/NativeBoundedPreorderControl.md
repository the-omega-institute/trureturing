# Native bounded preorder control

## Abstract

Exact finite fields realize the bounded path-selected parity controller.

**Definition 1.1 (Mode codes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.modeCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.modeCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The codes 0 through 6 denote VALUE, GUARD, POLL, UPDATE, HALT0, HALT1 and ERROR, respectively. Code 7 has no valid control.

**Definition 1.2 (Binary integer fields).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.fieldBits`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.fieldBits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An integer occupies the specified number of bits in least-significant-bit-first order. Arithmetic is modulo two to that width; the valid field bounds make this encoding injective.

**Definition 1.3 (Ordinary control width).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.bankWidth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.bankWidth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive h and candidate width e, the ordinary bank width is k=h+3+clog(2,h)+2 clog(2,h+1)+e. The h-1 path bits, path length, two visit counters, candidate, parity and three mode bits occupy exactly this width.

**Definition 1.4 (Candidate width).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.indexWidth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.indexWidth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Static and direct regimes use clog(2,T+1) bits. Active mode at positive T uses clog(2,2h) bits. Zero-width fields are allowed.

**Definition 1.5 (The displayed seven fields).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.controlBits`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.controlBits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenate the path right-padded with false to length h-1, the path length, branch count, leaf count, candidate index, parity bit and three mode bits. Padding follows the actual path and is zero.

**Definition 1.6 (Controls as finite banks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.encode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A bank is the finite set of positions whose displayed control bit is true. No additional mutable fields occur in this representation.

**Definition 1.7 (Valid-code inversion).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.decode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Among controls satisfying the installed field and mode conditions, decode the uniquely encoded control. A bank with no such control denotes canonical ERROR. This finite table specification depends only on the installed constants and bank bits.

**Definition 1.8 (Raw reply columns).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.flagReply`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.flagReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four source replies alpha, beta, branch and absent occupy flag columns zero through three. The remaining flag column is interpreted as absent only by this auxiliary map; rowTable handles unsupported columns separately.

**Definition 1.9 (The fixed instruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.opcode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.opcode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Forget the successors of the source-blind control program. Keep its literal Read address, genuine Update or fixed Halt bit. HALT1 has true output and HALT0 has false output.

**Definition 1.10 (The full finite table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.rowTable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.rowTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a bank, decode the displayed control and install its opcode. Every typed Read column uses the control program successor and encodes its fields. The Update acknowledgement uses its Update successor. Every unsupported column selects canonical ERROR. Sources, histories and pending subtrees are absent from the selector.

**Definition 1.11 (Exact polling Read count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.PollingRun`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.PollingRun` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This mathematical execution relation uses the same actual intermediate Read and Update rows, and labels each finite path with the number of Reads executed in POLL mode. Labels are not fields of the controller. A Read increments the label exactly in POLL; Update preserves it.

**Definition 1.12 (Exact valid and invalid field codes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.TableContract`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.TableContract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every valid control has exactly k displayed bits and decodes back to itself. Every bank outside the image of valid controls reads the root and sends every response column to canonical ERROR.

**Definition 1.13 (Paid physical behavior).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.PhysicalRealization`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.PhysicalRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Install the total two-bank table with zero flags, phase zero, the encoded initial control in the first bank and the other bank empty. There are exactly 2^(2k+8) words of width 4k+15. Every installed word has no adjacent true bits, and each response holds or changes one bit. A transfer executes the original primitive followed only by the displayed charged root Reads and introduces no extra Update. Its exact primitive count is the source and destination bank weights plus 5 or 7, according to the ready bank, hence at most 2k+7. An actual execution reaches the fixed-output Halt at the same source epoch as the source table. All word and physical executions ending at Halt have that endpoint and epoch. The remaining finite trace length is a rank, vanishes at Halt and decreases by one per primitive on terminating support. Its value depends only on the current source and word, independently of their historical representation.

**Definition 1.14 (Uniform bounded control contract).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.Specification`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.Specification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix h,T,t,u and a Boolean active setting. Use rowParameters, indexWidth and rowInitial depending only on h,T and the setting. The actual Update count U is mathematical comparison data. The contract gives exact fields, the licensed stationary interval, a concrete encoded source Run to the selected canonical Halt, its fixed output, and all finite source-prefix controls. Each such control is valid, is outside ERROR and satisfies RowPoint: it is canonical polling control or retains a proper bounded trial prefix with its exact compressed frontier and counters. The contract also includes PhysicalRealization for this same table and actual entry source. A terminating PollingRun has exactly U+1 POLL Reads in active mode at positive T, and zero POLL Reads in the other regimes. Every N at most t+U also has the complete TrialSpec on the stationary source, including its actual image equation, ordered producer prefix, accepted guards, decoded replies and query bounds. Each actual trial point retains such an N before a decoder call.

**Theorem 1.15 (The installed bounded parity controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.native_bounded_preorder_control`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.native_bounded_preorder_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every h,T,t and finite full source u of length h, with t at most T and either T zero or h even, either Boolean active setting satisfies Specification with bit true exactly when the beta-leaf count of u is odd. Thus one source-independent table and initial bank work uniformly for all promised sources and historical epochs. Static and direct execution use no Updates; active execution at positive T uses the single-Update polling rows and then the short candidate interval. The real path-selected trial execution supplies the concrete Run used by the physical implementation.

The valid field bounds place every integer below its binary capacity. Equality of banks therefore recovers each field, including the unpadded path. The total bit table agrees step for step with the path-selected program on actual source replies. Induction on a terminating program execution both constructs the encoded execution and recovers every finite encoded prefix. The compressed frontier relation then gives each real query, candidate reset and final parity. A two-valued phase potential is zero in POLL and one elsewhere. Its balance with the real Update epoch counts precisely U+1 polls before the stationary traversal. Applying the two-bank execution theorem to the concrete Run yields the physical execution, legal rows, first Halt and rank.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.PhysicalRealization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.PollingRun`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.Specification`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.TableContract`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.bankWidth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.controlBits`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.decode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.encode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.fieldBits`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.flagReply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.indexWidth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.modeCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.native_bounded_preorder_control`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.opcode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderControl.rowTable`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows](NativeBoundedPreorderRows.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord](../../../../ObserverMemory/Algorithms/TwoBankInstalledWord.md)
