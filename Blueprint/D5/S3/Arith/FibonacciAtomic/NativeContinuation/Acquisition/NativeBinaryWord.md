# Original native binary word acquisition

## Abstract

Binary output of the original successful word and complete suffix table.

The original guard forbids a true seam followed by a window with a true last bit. The successor is the window first bit. Distinct modes retain separate permission bits even when they share a successor.

The acquired table is retained unchanged while a physical scan accumulates the positivity of each of its two binary counts. The first allowed mode with positive child count supplies the next original window. The existing natural reconstruction theorem connects those choices to the original histories and integer reader.

The complete execution includes the seam read, input copy, backward table, actual zero test, permission reads, window writes and final table and word output. The counted stack execution is bounded by 4096 times (L+1) squared. The existing binary simulation turns this into a single quartic bound for the same complete program.

**Definition 1.1 (Control).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.Control`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.Control` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite labels retain a seam, two positivity flags, a five-mode permission mask and a bounded position inside a mask or a printed window. No label stores a horizon or an unbounded word.

**Definition 1.2 (walk).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.walk`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.walk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The controller pops the actual seam, scans the marked binary counts, rejects a zero initial count, and otherwise selects the first allowed mode whose child count is positive. It pushes the original low, middle, high bits of each selected window.

**Definition 1.3 (walkEncoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.walkEncoding`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.walkEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite product encoding directly reuses the existing row controller for finite masks and small positions. The inverse law holds on every reconstruction label.

**Definition 1.4 (printed).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.printed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.printed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each original window contributes its three low-to-high printed bits. The window order is the original high-to-low sequence, and all zero windows remain present.

**Definition 1.5 (input).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.input`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial seam bit precedes the two terminal membership bits and all five-bit restriction masks. The total input length is three plus five times the horizon.

**Definition 1.6 (readSeam).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.readSeam`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.readSeam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three primitive instructions read the seam and preserve it in an extra frame register while the backward table is acquired.

**Definition 1.7 (prepare).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.prepare`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.prepare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Physical clears, a preserving table copy and a saved-input reversal install the forward restriction stream and the table scan. All cleared storage and all transfers are counted.

**Definition 1.8 (finish).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.finish`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.finish` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Physical transfers preserve the complete table as an output prefix and append the decision bit and the reconstructed word. Failure has a false status and no word bits; the successful empty word has a true status.

**Definition 1.9 (program).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.program`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.program` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One fixed finite program reads the seam, preserves the explicit input, acquires the full table using the existing table program, reconstructs or reports failure, and writes the combined output.

**Definition 1.10 (encoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.encoding`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.encoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite sums and products combine the seam reader, preserving copy, table program, preparation, reconstruction and output continuations.

**Definition 1.11 (stackMachine).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.stackMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.stackMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing finite-instruction compiler produces the counted nine-register Boolean-stack machine.

**Definition 1.12 (binaryMachine).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.binaryMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.binaryMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing single-tape binary compiler supplies the actual machine, including input initialization, storage, access, control and physical output.

**Definition 1.13 (output).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.output`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.output` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All original suffix rows form the output prefix. The following status bit and low-to-high window codes encode the original deterministic reconstruction result.

**Definition 1.14 (decodeWord).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.decodeWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.decodeWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Groups of three printed bits decode to the five original windows; other bit triples and incomplete triples are rejected.

**Definition 1.15 (decodeAnswer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.decodeAnswer`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.decodeAnswer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The status bit distinguishes failure from a successful word of length zero. Successful payloads decode using the original three-bit window codes.

**Theorem 1.16 (native_binary_word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.native_binary_word`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.native_binary_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite horizon L, explicit family A of original allowed-window sets, terminal set B and initial seam s, the same fixed binary program reads exactly 3+5L bits. It outputs every original successful-suffix count for both seams, each bounded by five to the remaining horizon, then reports failure exactly when the initial count is zero. A positive count yields an actual allowed length-L word ending in B, with the original NativeHistory and rawMachine 0 execution. The physically printed table prefix and word payload decode exactly. One universal bound of 1073741824 times (L+1) to the fourth power covers the complete binary execution, including initialization, all integer work, table and word storage, access, control and output. The theorem includes the empty horizon, both seams, empty or full terminal sets, empty restrictions and zero rows. It makes no random sampling assertion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.Control`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.binaryMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.decodeAnswer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.decodeWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.encoding`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.finish`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.input`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.native_binary_word`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.output`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.prepare`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.printed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.program`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.readSeam`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.stackMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.walk`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryWord.walkEncoding`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable](NativeBinaryTable.md)
