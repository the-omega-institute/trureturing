# Original native binary table

## Abstract

Physical binary acquisition of the original suffix table.

The original high-to-low guard and first-bit successor are inherited from the native row program. Distinct modes remain separate contributions. The explicit input includes all terminal and restriction bits.

The backward loop retains every binary row, including all zero rows, while each row width grows by three columns. A false header and true data markers separate rows without reserving a count value. The complete output has quadratic length.

The counted execution pays for input movement, terminal initialization, every restriction scan, every row instruction, table copies, control and final output movement. The single-tape compiler also pays for physical storage, access and initialization. The theorem is universal in the horizon; it does not implement successful-word output.

**Definition 1.1 (mask).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.mask`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.mask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five membership bits follow zero, low, middle, high, ends. Each mode retains its own bit.

**Definition 1.2 (terminalColumns).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.terminalColumns`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.terminalColumns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The single terminal column contains the two indicators of membership in B.

**Definition 1.3 (row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.row`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting at the terminal column, row applies the original binary recurrence from the last restriction to the first. Its width is one plus three times the remaining horizon.

**Definition 1.4 (rows).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.rows`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list contains the current-to-terminal binary rows, including the terminal row when the horizon is zero.

**Definition 1.5 (pack).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.pack`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.pack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The false header precedes high-to-low data bits, each marked by true. The original row can therefore contain arbitrary zero bits.

**Definition 1.6 (records).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.records`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.records` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The table stores every packed serialized row in current-to-terminal order. No row is dropped when both counts vanish.

**Definition 1.7 (input).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.input`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two terminal membership bits precede the explicit five-bit masks in backward processing order. The length is two plus five times the horizon.

**Definition 1.8 (saveScan).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.saveScan`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.saveScan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A primitive pop and three pushes per data bit copy the row into the retained table and scratch, followed by the row header.

**Definition 1.9 (save).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.save`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.save` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scratch transfer restores the current row after saving it. A row with n bits costs exactly six times n plus five stack instructions.

**Definition 1.10 (saveEncoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.saveEncoding`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.saveEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum of the existing finite scan and transfer label encodings.

**Definition 1.11 (rowRegister).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.rowRegister`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.rowRegister` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original row registers map injectively to registers zero and two in the seven-register table program.

**Definition 1.12 (advanceProgram).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.advanceProgram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.advanceProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original row program is lifted into the table frame. It preserves the restriction stream, retained table, scratch and saved restriction bits.

**Definition 1.13 (loadMask).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.loadMask`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.loadMask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Five permission bits are physically popped and saved, and their decoded mask is prepended to the current child row by five literal pushes. Empty remaining input terminates the loop.

**Definition 1.14 (body).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.body`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.body` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A permission load, original binary row execution and physical table save form one guarded iteration.

**Definition 1.15 (bodyEncoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.bodyEncoding`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.bodyEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original finite row label encoding is reused for both the permission parser and row program; the save labels use a finite sum.

**Definition 1.16 (initProgram).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.initProgram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.initProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The terminal bits are physically popped from the input stream and pushed onto the initial row in false-seam then true-seam order.

**Definition 1.17 (program).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.program`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.program` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed program moves the actual input, initializes the terminal row, saves it, repeats the guarded backward body, and moves the complete retained table to the physical output register.

**Definition 1.18 (encoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.encoding`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.encoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite sum and product encodings combine all controller labels. No label contains an unbounded word or counter.

**Definition 1.19 (stackMachine).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.stackMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.stackMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing instruction compiler builds a fixed Boolean-stack machine from program and encoding.

**Definition 1.20 (binaryMachine).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.binaryMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.binaryMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing stack compiler produces a fixed single-tape binary machine, including input initialization and physical output.

**Definition 1.21 (read).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.read`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.read` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given an explicit row bit width and retained table bits, read removes the header and markers, reverses the high-to-low payload and decodes the original two counts.

**Definition 1.22 (decodeTable).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.decodeTable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.decodeTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The known horizon determines each row width. Decoding successively addresses every original row, without a supplied count certificate.

**Definition 1.23 (regs).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.regs`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.regs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The table frame stores the current row, input stream, retained table, scratch and restriction history in seven explicit Boolean registers.

**Theorem 1.24 (row_value).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.row_value`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.row_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding the original recursively computed binary row gives the exact original pair of suffix counts.

**Theorem 1.25 (pack_length).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.pack_length`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.pack_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A packed row with n bits has one header and two physical bits for each data bit.

**Theorem 1.26 (exec_table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.exec_table`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.exec_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete fixed table program starts with the explicit input, physically produces all packed rows in register zero, and uses at most 256 times the square of the horizon plus one stack instructions.

**Theorem 1.27 (Physical acquisition of every original suffix row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.native_binary_table`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.native_binary_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem native_binary_table (L : ℕ) (A : Fin L → Finset Window) (B : Finset Bool) :     let as := List.ofFn A     (input B as).length = 2 + 5 * L ∧     (records B as).length = (L + 1) * (6 * L + 5) ∧     decodeTable L (records B as) = table B as ∧     (∀ (t : Fin (L + 1)) (s : Bool),       (decodeTable L (records B as))[t.val]? = some (counts B (as.drop t.val)) ∧       entry (counts B (as.drop t.val)) s = (completions B (as.drop t.val) s).card ∧       entry (counts B (as.drop t.val)) s ≤ 5 ^ (L - t.val)) ∧     ∃ time tape, time ≤ 2097152 * (L + 1) ^ 4 ∧       Complexity.runInput binaryMachine time (input B as) = some (true, tape) ∧       tape.output = records B as

The decoded output equals the original natural suffix table at every position. Each entry counts original successful words and is bounded by five to the remaining horizon. The physical program runs within 2097152 times the fourth power of the horizon plus one. Its complete counted stack execution, including all row storage and output, is bounded by 256 times the square of the horizon plus one.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.advanceProgram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.binaryMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.body`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.bodyEncoding`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.decodeTable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.encoding`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.exec_table`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.initProgram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.input`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.loadMask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.mask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.native_binary_table`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.pack`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.pack_length`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.program`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.read`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.records`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.regs`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.row`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.rowRegister`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.row_value`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.rows`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.save`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.saveEncoding`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.saveScan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.stackMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryTable.terminalColumns`
- Dependency: [D5/S0/Computability/BinaryMachine/StackControl](../../../../../S0/Computability/BinaryMachine/StackControl.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackFrame](../../../../../S0/Computability/BinaryMachine/StackFrame.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow](NativeBinaryRow.md)
