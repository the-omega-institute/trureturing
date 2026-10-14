# Original vector recovery by a complete legal word

## Abstract

InterleavedWordRecovery

**Definition 1.1 (Complete promised source family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.original`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.original` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cut is the entire level of addresses of length m = clog 2 h, including unselected leaves. At selected address q i numerical false is original zero, hence source alpha (true); numerical true is original one, hence source beta (false). Every unselected leaf is alpha. The ordered injective selection and complete skeleton are common promised input, rather than acquired shape evidence. Every full vector is allowed, including all-alpha sources outside the alpha orbit. At h = 1 the root is the selected leaf.

**Definition 1.2 (Native Q, U and Z table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.program`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.program` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q s reads q at index length s followed by length s divided by two right steps. At even epochs alpha and beta decode to zero and one; at odd epochs beta and branch decode to zero and one. The total four-valued response table holds Q s for unsupported replies, including absence. A supported Read appends one bit and enters U s or the final Z s. U s performs exactly one genuine substitution on the same source and enters Q s. Z s halts with its fixed full vector. The initial vertex is Q empty for every source.

**Definition 1.3 (Alternating block level coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.encode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each zero-based Read index i, coordinates 5i and 5i+1 record zero and one. Coordinate 5i+3 records the following Update, when present. Coordinates of residues two and four remain zero. Earlier blocks stay activated and later blocks stay zero. The final Read block has no following separator or Update. The exact width is 5h-3. This is the source's explicit level-coordinate construction, an application of the classical Havel–Moravek method, rather than an independent graph-theory result.

**Definition 1.4 (Exact installed image).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.Installed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.Installed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Installed h consists precisely of encode applied to all Q, U and Z vertices. No ambient word has an instruction row. The inverse is an immutable table lookup. It does not introduce a persistent decoded vertex.

**Definition 1.5 (Word-only row selection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.wordProgram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.wordProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The only mutable controller argument is one Installed word. Its row chooses the instruction, materialized literal, immediate response word and fixed full output. Source, prefix support, epoch, rank and trace are proof coordinates and are unavailable to row selection. The proof uses NativeSerialMachine.Run and nativeStep for both representations, preserving the same physical source, chronological raw replies, source successors and first full Halt.

In the formula, m abbreviates clog 2 h; FullVectors h is the subtype of Boolean lists of length h; u x abbreviates original m q x; T x abbreviates chronology q 0 x; Q, U and Z omit proof-irrelevant bound fields. E is encode, I is install, J is inverse, and liftConfig changes only the vertex to its installed word. readCount is the length of answers; updateCount counts update events; Reached is nativeStep reachability from the common initial vertex, epoch zero, the original source and empty trace. ReachedVertices is the subtype of vertices for which some current register is actually reached from the fixed original u x. The displayed word reachability uses the corresponding installed initial word. These notations denote the actual definitions, not additional hypotheses or execution certificates.

**Theorem 1.6 (Full native recovery and exact word realization).**

$$\forall h: Nat, ((0 < h) \implies (\forall q: \operatorname{Fin}\left(h\right) \to Address, ((\operatorname{Injective}\left(q\right)) \implies ((\forall i: \operatorname{Fin}\left(h\right), (\operatorname{length}\left(\operatorname{q}\left(i\right)\right) = \operatorname{clog}\left(2, h\right))) \implies ((\operatorname{Injective}\left(\lambda x: \operatorname{FullVectors}\left(h\right), (\operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, \operatorname{value}\left(x\right)\right))\right)) \land (\forall x: \operatorname{List}\left(Bool\right), (\forall a: Address, (((\operatorname{length}\left(a\right) = \operatorname{clog}\left(2, h\right)) \land (\forall i: \operatorname{Fin}\left(h\right), (\operatorname{q}\left(i\right) \neq a))) \implies (\operatorname{subtree}\left(a, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right)\right) = \operatorname{some}\left(\operatorname{alpha}\left(\right)\right))))) \land (\forall x: \operatorname{List}\left(Bool\right), (\forall i: \operatorname{Fin}\left(h\right), (\operatorname{subtree}\left(\operatorname{q}\left(i\right), \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right)\right) = \operatorname{some}\left(\operatorname{of}\left(\operatorname{not}\left(\operatorname{getD}\left(x, \operatorname{value}\left(i\right), false\right)\right)\right)\right)))) \land (\forall x: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(x\right) = h) \implies ((\operatorname{Run}\left(\operatorname{program}\left(q\right), \operatorname{initial}\left(h\right), 0, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right), \operatorname{chronology}\left(q, 0, x\right), x\right)) \land (\operatorname{Run}\left(\operatorname{wordProgram}\left(q\right), \operatorname{install}\left(\operatorname{initial}\left(h\right)\right), 0, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right), \operatorname{chronology}\left(q, 0, x\right), x\right)) \land (\forall t: Trace, (\forall z: \operatorname{List}\left(Bool\right), ((\operatorname{Run}\left(\operatorname{wordProgram}\left(q\right), \operatorname{install}\left(\operatorname{initial}\left(h\right)\right), 0, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right), t, z\right)) \implies ((t = \operatorname{chronology}\left(q, 0, x\right)) \land (z = x))))) \land (\operatorname{readCount}\left(\operatorname{chronology}\left(q, 0, x\right)\right) = h) \land (\operatorname{length}\left(\operatorname{chronology}\left(q, 0, x\right)\right) = 2\cdot h-1) \land (\operatorname{updateCount}\left(\operatorname{chronology}\left(q, 0, x\right)\right) = h-1) \land (\operatorname{localStep}\left(\right) \neg \in \operatorname{chronology}\left(q, 0, x\right)) \land (\operatorname{card}\left(\operatorname{ReachedVertices}\left(h, q, x\right)\right) = 2\cdot h)))) \land (\forall x: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(x\right) = h) \implies (\forall v: \operatorname{Vertex}\left(h\right), (\forall r: Source, ((\operatorname{Reached}\left(q, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right), v, r\right)) \iff ((\operatorname{Fits}\left(v, x\right)) \land (r = \operatorname{iterate}\left(substitution, \operatorname{epochOf}\left(v\right), \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right)\right)))))))) \land (\operatorname{card}\left(\operatorname{Vertex}\left(h\right)\right) = 3\cdot \operatorname{pow}\left(2, h\right)-3) \land (\operatorname{card}\left(\operatorname{Installed}\left(h\right)\right) = 3\cdot \operatorname{pow}\left(2, h\right)-3) \land (\forall w: \operatorname{Installed}\left(h\right), (\operatorname{Adm}\left(5\cdot h-3, \operatorname{value}\left(w\right)\right))) \land (\operatorname{Injective}\left(\operatorname{encode}\left(h\right)\right)) \land (\forall s: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(s\right) < h) \implies (\forall b: Bool, (\operatorname{hammingDist}\left(\operatorname{encode}\left(\operatorname{Q}\left(s\right)\right), \operatorname{encode}\left(\operatorname{child}\left(s, b\right)\right)\right) = 1)))) \land (\forall s: \operatorname{List}\left(Bool\right), (((0 < \operatorname{length}\left(s\right)) \land (\operatorname{length}\left(s\right) < h)) \implies (\operatorname{hammingDist}\left(\operatorname{encode}\left(\operatorname{U}\left(s\right)\right), \operatorname{encode}\left(\operatorname{Q}\left(s\right)\right)\right) = 1))) \land (\forall s: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(s\right) < h) \implies (\forall r: Reply, ((\operatorname{decode}\left(\operatorname{length}\left(s\right), r\right) = \operatorname{none}\left(\right)) \implies ((\operatorname{response}\left(s, r\right) = \operatorname{Q}\left(s\right)) \land (\operatorname{hammingDist}\left(\operatorname{encode}\left(\operatorname{Q}\left(s\right)\right), \operatorname{encode}\left(\operatorname{response}\left(s, r\right)\right)\right) = 0)))))) \land (\forall w: \operatorname{Installed}\left(h\right), (\exists x: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(x\right) = h) \land (\exists e: Nat, (\exists r: Source, (\exists t: Trace, (\operatorname{Reaches}\left(\operatorname{nativeStep}\left(\operatorname{wordProgram}\left(q\right)\right), \operatorname{tuple}\left(\operatorname{install}\left(\operatorname{initial}\left(h\right)\right), 0, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right), \operatorname{emptyTrace}\left(\right)\right), \operatorname{tuple}\left(w, e, r, t\right)\right)))))))) \land (\forall s: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(s\right) < h) \implies (\operatorname{wordProgram}\left(q, \operatorname{install}\left(\operatorname{Q}\left(s\right)\right)\right) = \operatorname{Read}\left(\operatorname{literal}\left(q, \operatorname{length}\left(s\right)\right), \lambda r: Reply, (\operatorname{install}\left(\operatorname{response}\left(s, r\right)\right))\right)))) \land (\forall s: \operatorname{List}\left(Bool\right), (((0 < \operatorname{length}\left(s\right)) \land (\operatorname{length}\left(s\right) < h)) \implies (\operatorname{wordProgram}\left(q, \operatorname{install}\left(\operatorname{U}\left(s\right)\right)\right) = \operatorname{Update}\left(\operatorname{install}\left(\operatorname{Q}\left(s\right)\right)\right)))) \land (\forall s: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(s\right) = h) \implies (\operatorname{wordProgram}\left(q, \operatorname{install}\left(\operatorname{Z}\left(s\right)\right)\right) = \operatorname{Halt}\left(s\right)))) \land (\forall w, c: \operatorname{Installed}\left(h\right), (\operatorname{wordProgram}\left(q, w\right) \neq \operatorname{localStep}\left(c\right))) \land (\operatorname{Injective}\left(\lambda x: \operatorname{List}\left(Bool\right), (\operatorname{answers}\left(\operatorname{chronology}\left(q, 0, x\right)\right))\right)) \land (\forall x: \operatorname{List}\left(Bool\right), ((\operatorname{length}\left(x\right) = h) \implies (\forall w: \operatorname{Installed}\left(h\right), (\forall r: Source, ((\exists e: Nat, (\exists t: Trace, (\operatorname{Reaches}\left(\operatorname{nativeStep}\left(\operatorname{wordProgram}\left(q\right)\right), \operatorname{tuple}\left(\operatorname{install}\left(\operatorname{initial}\left(h\right)\right), 0, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right), \operatorname{emptyTrace}\left(\right)\right), \operatorname{tuple}\left(w, e, r, t\right)\right)))) \iff ((\operatorname{Fits}\left(\operatorname{inverse}\left(w\right), x\right)) \land (r = \operatorname{iterate}\left(substitution, \operatorname{epochOf}\left(\operatorname{inverse}\left(w\right)\right), \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right)\right)))))))) \land (\forall v: \operatorname{Vertex}\left(h\right), (\forall e: Nat, (\forall r: Source, (\forall t: Trace, (\operatorname{nativeStep}\left(\operatorname{wordProgram}\left(q\right), \operatorname{tuple}\left(\operatorname{install}\left(v\right), e, r, t\right)\right) = \operatorname{map}\left(\operatorname{nativeStep}\left(\operatorname{program}\left(q\right), \operatorname{tuple}\left(v, e, r, t\right)\right), \operatorname{liftConfig}\left(h\right)\right)))))) \land (\forall x: \operatorname{List}\left(Bool\right), (\forall a: Address, ((\operatorname{length}\left(a\right) = \operatorname{clog}\left(2, h\right)) \implies (\operatorname{subtree}\left(a, \operatorname{original}\left(\operatorname{clog}\left(2, h\right), q, x\right)\right) = \operatorname{some}\left(\operatorname{leafValue}\left(q, x, a\right)\right))))) \land (\forall u: Source, (\operatorname{substitution}\left(u\right) \neq u)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.interleaved_word_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete family construction uses ActualCutPartitionRecovery.prefixTrie and its original prefixTrie_at theorem. NativeDepthPatterns.original_present_transport and the unrestricted append-readout component of ActualLeafHistoryRigidity.actual_address_geometry preserve navigation. DelayedOriginalReadout.right_clock_iterate and right_clock_readout supply the reply clocks and genuine-update witness. NativeSerialDepth.run_unique supplies labeled trace and output uniqueness. Pinned finite-cardinality and Hamming facts normalize the resulting exact counts; admissibility uses AdmissibleCount.Adm and ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true.

The new inference constructs the source-independent table and its actual native Run, proves both directions of actual Q/U/Z supports, and realizes exactly their installed legal image. Every allowed prefix has a promised completion, including every unary Update position and every fixed full-output halt. The installed union has 3 times 2 to h minus 3 states; one source visits exactly 2h states. Each supported primitive changes exactly one word bit, unsupported replies hold, and the first full Halt immediately follows the final primitive with no local step or intermediate output.

This is conditional mathematical installation under Definition 1.3's initialization, immutable lookup, literal delivery, native primitive execution, immediate response-write and fixed full-output services. It establishes neither their physical availability nor free setup. It asserts no optimal total cost or minimum width. The old and classical widths and U(h), arbitrary-competitor Read lower bound, Fibonacci and Theta(h) claims, literal/union/service bills and the whole parent theorem remain outside this result. The word execution clause is this explicit code instance; the generic obligations for arbitrary chosen codes in Verification 4.3 are not claimed.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.Installed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.encode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.interleaved_word_recovery`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.original`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.program`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.wordProgram`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout](../DelayedOriginalReadout.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth](../NativeSerialDepth.md)
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](../../../../Quantum/FockSpace/ForbiddenNeighbourDeterminant.md)
