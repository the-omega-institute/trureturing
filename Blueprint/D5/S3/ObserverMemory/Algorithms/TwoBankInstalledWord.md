# Two-Bank Installed Word

## Abstract

Two-bank routing realizes each native source instruction by charged one-bit responses.

**Definition 1.1 (Bank contents).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Bank`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Bank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A k-bit bank is a finite subset of Fin k; membership is its Boolean bit.

**Definition 1.2 (Five reply flags).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Flag`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Flag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five indices distinguish the four native read replies and the update acknowledgement.

**Definition 1.3 (Literal addresses).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Address`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Address` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Addresses are finite Boolean lists, including the empty root address.

**Definition 1.4 (Source instructions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Opcode`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Opcode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An instruction reads one literal address, performs one update, or halts with a fixed Boolean output.

**Definition 1.5 (Typed source replies).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Typed`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Typed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read replies use flags zero through three; an update uses flag four. A halt has no typed reply.

**Definition 1.6 (Complete mutable word).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Word`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word contains exactly two k-bit banks, all five flag bits, and one of eight phase values. Arbitrary flag patterns and all phase patterns are present.

**Definition 1.7 (Fixed source table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Table`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A table assigns an instruction to every bank value and a successor bank to every flag. No particular source algorithm or initial encoding is assumed.

**Definition 1.8 (Least differing bit).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.toward`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.toward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If two banks differ, the least position in their symmetric difference is flipped; otherwise the bank is retained.

**Definition 1.9 (Singleton flag decoder).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.singleFlag`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.singleFlag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly singleton flag sets decode to a reply flag. Empty sets and multiple flags do not.

**Definition 1.10 (Installed instruction row).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Row`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each word has one instruction and one next word for each flag. Only replies typed for that instruction are actual native responses.

**Definition 1.11 (Total installed table).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The phase cycle is 000, 001, 011, 010, 110, 111, 101, 100, then 000. Ready rows execute the source instruction; routing rows read the root, fill the destination bank, erase the old bank, and reset the flag. Unsupported rows read the root and hold.

**Definition 1.12 (Two ready encodings).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.ready`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.ready` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left encoding stores the control in bank A at phase 000; the right encoding stores it in bank B at phase 010. The other bank and all flags are zero.

**Definition 1.13 (Paid routing paths).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Routing`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Routing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every routing edge installs a root read and gives the same successor for every raw reply. The natural index counts these calls.

**Definition 1.14 (One logical change).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Change`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Change` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A change flips one bank bit, one flag bit, or advances one step of the eight-phase cycle.

**Definition 1.15 (Logical positions).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Slot`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Slot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positions list the first bank, the second bank, the five flags, and the three phase bits.

**Definition 1.16 (Gray phase bits).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.phaseBits`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.phaseBits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The eight phase values encode the stated cyclic Gray order; consecutive phases differ in exactly one bit, including the last-to-first transition.

**Definition 1.17 (Logical word projection).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.logical`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.logical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bank and flag membership give their bits; the phase contributes its three Gray bits.

**Definition 1.18 (One Boolean coordinate changes).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.OneBit`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.OneBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is one position whose Boolean value is complemented, and every other position is retained.

**Definition 1.19 (Contiguous slot order).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.slotIndex`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.slotIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite equivalence numbers the bank, flag, and phase positions consecutively.

**Definition 1.20 (Zero interleaving).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.interleave`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.interleave` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Logical bits occupy the even positions and every odd position is zero. The physical length is twice the logical length minus one.

**Definition 1.21 (Physical word).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physical`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordered logical bits are interleaved with fixed zeros. For bank width k the length is 4k plus 15.

**Definition 1.22 (Phase decoding).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.phaseIndex`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.phaseIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All eight three-bit patterns decode to their phase indices.

**Definition 1.23 (All patterns are represented).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.logicalEquiv`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.logicalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word type is equivalent to all Boolean assignments on its logical slots; unsupported combinations are included.

**Definition 1.24 (Full installed image).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installedWords`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installedWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The installed finite set is the complete image of physical encoding, containing exactly 2^(2k + 8) words.

**Definition 1.25 (Four native read replies).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.RawReply`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.RawReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Raw read replies have four values; update acknowledgement is represented separately.

**Definition 1.26 (Read flag embedding).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.replyFlag`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.replyFlag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A raw reply maps to the corresponding one of the first four flags.

**Definition 1.27 (Actual primitive chronology).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Event`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Event` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A read event records its literal address and actual reply; an update is a distinct event. Padding root reads remain in the chronology.

**Definition 1.28 (Charged one-bit execution).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Execution`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Execution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every read follows the observation at the current epoch and records its reply. Every update advances the epoch once. Each immediate response changes one physical bit.

**Definition 1.29 (Native source program).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.sourceProgram`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.sourceProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source table becomes a native program with bank-valued controls, preserving read literals, typed successors, and halt locations.

**Definition 1.30 (Native installed program).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.wordProgram`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.wordProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete word is the native control. Installed rows determine all instructions and successors.

**Definition 1.31 (Physical control carrier).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Installed`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Installed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A physical control is a word in the full installed image.

**Definition 1.32 (Physical encoding equivalence).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalEquiv`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Physical encoding is a bijection from complete logical words to installed physical controls.

**Definition 1.33 (Physical row instruction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalInstruction`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalInstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unique decoded word selects the fixed instruction at each physical control.

**Definition 1.34 (Physical native program).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalProgram`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport through the physical equivalence preserves native observations and epochs without changing literal addresses.

**Definition 1.35 (Halting execution data).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.TerminatesWith`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.TerminatesWith` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A configuration terminates with a trace when that trace reaches an installed halt. This predicate is proof data and is not consulted by a row.

**Definition 1.36 (Remaining primitive calls).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.remaining`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.remaining` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If a terminating trace exists, its length defines the remaining-call count. Otherwise this total definition returns zero, which by itself does not assert termination.

**Definition 1.37 (Native reply encoding).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.rawReply`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.rawReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four source-tree replies are encoded in the fixed flag order.

**Definition 1.38 (Observation of the current source).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.actualObservation`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.actualObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation at epoch n reads the source after n substitutions. Only updates advance that epoch.

**Definition 1.39 (Rank at the current source).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.sourceRank`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.sourceRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The remaining-call count is evaluated from the supplied actual source at epoch zero.

**Definition 1.40 (History-independent rank).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.SourceRankInvariant`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.SourceRankInvariant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two terminating executions with the same observer word and equal actual sources have equal remaining-call counts, even if their histories and epoch numbers differ.

**Theorem 1.41 (Exact transfer between ready banks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.typed_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.typed_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every width k, table T, ready direction, bank z, and reply r typed for the source instruction, the ready row installs that same instruction. After its reply writes the flag, a root-read routing path reaches the opposite ready encoding of the successor bank. Its exact length is the weight of z plus the weight of the successor plus four in the left-to-right direction and plus six in the reverse direction. Including the source instruction gives five and seven, respectively. Filling and erasing proceed by least differing bits; the endpoint has the old bank and all flags reset.

**Theorem 1.42 (Every total row holds or changes one bit).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed_local`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every table, word, and flag, the selected successor either equals the original word or satisfies the logical one-bit change relation. This includes unsupported words and does not require reachability or a typed-reply premise.

**Theorem 1.43 (Sparse rows and physical one-bit responses).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physical_rows`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physical_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every table, word, and flag, neither the word nor its selected successor has adjacent occupied physical positions. The successor either holds the logical word or changes exactly one physical bit. The assertions apply to the entire installed image.

**Theorem 1.44 (Native events and epochs are preserved).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.native_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.native_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every observation field, ready direction, bank and starting epoch, a read instruction has an installed execution whose first event is that exact read and actual reply, followed by the counted root reads at the same epoch. An update has an execution whose first event is an update, followed by the counted root reads at the incremented epoch. Each response changes one physical bit; there are no additional updates.

**Theorem 1.45 (Simulation of every supplied finite source run).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.simulate_run`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.simulate_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite source Run, on one observation field from a bank and epoch to another bank and epoch, yields a finite installed Execution between ready encodings at the same endpoint epochs. The initial ready direction is arbitrary. The final direction and full primitive event list are supplied by the construction.

**Theorem 1.46 (Conditional halt transport and remaining-call rank).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed_halt`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed_halt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a finite source Run reaches a bank whose instruction halts with a fixed bit. For either initial ready direction, the installation contains exactly 2^(2k + 8) words of physical length 4k plus 15; every transfer uses at most 2k plus 7 primitives, and every row is sparse and holds or changes one bit. There exist a final ready direction and an installed event trace reaching that same fixed halt output. Every halt-ended logical Run from the entry has this endpoint and epoch; physical transport has the same existence and endpoint uniqueness. The entry rank equals the event-list length, the final rank is zero, and each reachable prefix has an execution suffix whose length equals its remaining rank. Every one-event step with a terminating suffix decreases that rank by one. Equal actual sources give history-independent ranks under the two supplied termination hypotheses. This theorem assumes the source run and halt premise: it supplies neither a particular source instruction table, its initial-word encoding, nor unconditional termination or source and storage resource bills.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Address`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Bank`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Change`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Event`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Execution`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Flag`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Installed`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.OneBit`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Opcode`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.RawReply`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Routing`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Row`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Slot`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.SourceRankInvariant`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Table`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.TerminatesWith`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Typed`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.Word`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.actualObservation`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installedWords`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed_halt`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.installed_local`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.interleave`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.logical`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.logicalEquiv`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.native_transfer`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.phaseBits`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.phaseIndex`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physical`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalEquiv`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalInstruction`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physicalProgram`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.physical_rows`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.rawReply`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.ready`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.remaining`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.replyFlag`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.simulate_run`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.singleFlag`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.slotIndex`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.sourceProgram`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.sourceRank`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.toward`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.typed_transfer`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/TwoBankInstalledWord.wordProgram`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](../../Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/NativeExecutionTransport](NativeExecutionTransport.md)
