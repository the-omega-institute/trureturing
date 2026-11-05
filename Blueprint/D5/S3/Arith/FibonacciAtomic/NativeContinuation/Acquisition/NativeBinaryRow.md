# Binary original suffix row

## Abstract

Binary computation of an original suffix row.

The row recurrence uses the original high-to-low native reader: the incoming guard is not (s=true and last b=true), and the successor seam is first b. Distinct allowed modes contribute separately even when they have the same successor.

A single fixed finite-control binary transducer reads the five explicit permission bits and any finite interleaved binary child row. It computes both original guarded sums exactly. Its carries are bounded by four; three extra columns discharge the carry without truncation.

The instruction proof counts the permission scan, every bit read and write, carry draining, control jumps and output reversal. The existing compiler then supplies actual input initialization, stack storage and access simulation, and physical single-tape output. The resulting bit-time bound is universal in the child width.

This transducer computes one backward row. Acquiring a whole suffix table while retaining its entries and reconstructing a successful original word requires a larger program, whose runtime is not part of the single-row statement.

**Definition 1.1 (A pair of count bits).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Column`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Column is Bool times Bool: one bit for each original incoming seam.

**Definition 1.2 (The two finite carries).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Carry`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Carry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Carry is Fin 5 times Fin 5. Both carries belong to the finite program control and never store an unbounded integer.

**Definition 1.3 (Interleaved count representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.serialize`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.serialize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite list xs of bit pairs, serialize xs writes the false-seam bit and then the true-seam bit at each column. Columns are little endian.

**Definition 1.4 (Decoding paired columns).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.parse`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.parse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every bit list, parse groups successive bits into false-seam and true-seam columns. A final unmatched bit is ignored; the proved program output always has even length.

**Definition 1.5 (The represented child row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.value`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every column list xs, value xs applies the existing little-endian bitsValue to its two projections. Leading high zero columns remain allowed.

**Definition 1.6 (Reading a serialized row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.decode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.decode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every bit list bs, decode bs applies value to parse bs.

**Definition 1.7 (Explicit original restrictions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.input`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original allowed set a and finite child column list xs, input a xs contains five membership bits in the order zero, low, middle, high, ends, followed by serialize xs. No table, run certificate or resource evidence is part of the input.

**Definition 1.8 (One simultaneous binary column).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.round`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.round` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original allowed set a, two carries below five and input column p, round forms each original guarded sum of selected p bits plus its carry. The parity bits are output and the two quotients by two become the next carries. A five-term sum plus a carry below five is below ten.

**Definition 1.9 (Draining the finite carries).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.drain`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.drain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n and pair of carries c, drain n c serializes their next n binary columns by repeatedly taking parity and dividing by two.

**Definition 1.10 (The binary row function).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.columns`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.columns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every a, c and finite child row xs, columns a c xs scans round across all columns and then appends three drain columns. Three columns suffice for every carry below five, including zero.

**Definition 1.11 (Finite control labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Control`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Control` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The labels store a parser position below six, an original five-mode permission subset, two carries below five, at most one bit pair and a drain position below four. No label contains an input-sized word or natural-number counter.

**Definition 1.12 (Primitive counted instructions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.scanProgram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.scanProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

scanProgram uses only the supplied pop, push, goto and halt instructions on two Boolean stacks. It reads each of the five permission bits, scans both child bits, writes both result bits and drains the carries. An incomplete child pair or permission prefix fails.

**Definition 1.13 (Restoring output orientation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.program`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.program` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

program sequences scanProgram with the existing two-stack transfer routine. This physical reversal restores the original interleaved little-endian column order.

**Definition 1.14 (An explicit finite instruction table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.controlEncoding`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.controlEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

controlEncoding enumerates all masks as sublists of the original five modes and all finite label fields. The computable list index and lookup form a finite Encoding; one additional unused index decodes to the failure label.

**Definition 1.15 (Composed finite labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.encoding`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.encoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

encoding combines controlEncoding with the existing four-label transfer encoding using the supplied sum encoding.

**Definition 1.16 (The compiled Boolean-stack graph).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.stackMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.stackMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

stackMachine is the existing StackProgram compilation of program and its finite encoding. Its instructions inspect or change one bit on one of two stacks.

**Definition 1.17 (The physical binary transducer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.binaryMachine`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.binaryMachine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

binaryMachine is the supplied StackCompile compilation of stackMachine into the original single-tape machine, including input initialization and physical tape output.

**Theorem 1.18 (Serialized row length).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.serialize_length`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.serialize_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every xs : List Column, (serialize xs).length = 2 * xs.length.

**Theorem 1.19 (Exact paired decoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.parse_serialize`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.parse_serialize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every xs : List Column, parse (serialize xs) = xs.

**Theorem 1.20 (Output column width).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.columns_length`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.columns_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a : Finset Window, c : Carry and xs : List Column, (columns a c xs).length = xs.length + 3.

**Definition 1.21 (Two row registers).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.registers`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.registers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all src and dst : List Bool and j : Fin 2, registers src dst j is src when j = 0 and dst otherwise.

**Definition 1.22 (A permission bit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.insertBit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.insertBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every a : Finset Window, b : Window and v : Bool, insertBit a b v is insert b a when v is true and a otherwise.

**Theorem 1.23 (Exact instruction execution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.exec_program`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.exec_program` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a : Finset Window and xs : List Column, Exec program program.start (registers (input a xs) []) (8 * xs.length + 28) (true, registers (serialize (columns a (0,0) xs)) []). The complete original two-register execution is available for register-frame composition.

**Theorem 1.24 (Exact native row computation in quadratic bit time).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.native_binary_row`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.native_binary_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a : Finset original Window and every xs : List (Bool times Bool), input a xs has length 5 + 2 * xs.length; serialize (columns a (0,0) xs) has length 2 * (xs.length+3); its decode equals advance a (value xs); and there exist time and tape such that time <= 16384 * (xs.length+1)^2, Complexity.runInput binaryMachine time (input a xs) = some (true,tape), and tape.output = serialize (columns a (0,0) xs).

Simultaneous carry induction proves that both output values equal the corresponding original five-mode sums. The counted stack execution uses exactly 8 * xs.length + 28 instructions, including parsing and final reversal. StackCompile.simulate is applied to that proved execution; expanding its initialization and simulation budgets gives the stated quadratic bound. Empty rows, empty and full allowed sets, zero child values, repeated successor seams and arbitrary high zero padding are all within the quantifiers.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Carry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Column`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.Control`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.binaryMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.columns`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.columns_length`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.controlEncoding`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.decode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.drain`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.encoding`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.exec_program`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.input`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.insertBit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.native_binary_row`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.parse`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.parse_serialize`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.program`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.registers`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.round`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.scanProgram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.serialize`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.serialize_length`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.stackMachine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeBinaryRow.value`
- Dependency: [D5/S0/Computability/BinaryMachine/StackCompile](../../../../../S0/Computability/BinaryMachine/StackCompile.md)
- Dependency: [D5/S0/Computability/BinaryMachine/StackWords](../../../../../S0/Computability/BinaryMachine/StackWords.md)
- Dependency: [D5/S0/Computability/PhysicalDivider/WordArithmetic](../../../../../S0/Computability/PhysicalDivider/WordArithmetic.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition](NativeSuffixAcquisition.md)
