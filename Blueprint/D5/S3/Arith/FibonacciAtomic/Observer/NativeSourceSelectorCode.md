# Executable Numeric Selector

## Abstract

Closed executable numeric selector with exact raw-instruction and original-state realization laws.

**Definition 1.1 (Raw workspace instructions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.tickCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.tickCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The program uses the pinned Nat.Partrec.Code constructors. Products use Nat.pair, a list cell uses one plus the paired head and tail, and sums use doubled payloads with parity tags. Zero tests first use pairing and unpairing to make a zero-or-one counter; primitive recursion for this test then has at most one recursive step. Numeric scans test every Boolean in an address and every address-valued frame in the stack. The program replaces a failed control test by zero, the encoding of numericInitial. Its visit branch constructs the complete read address and four continuations, including the absent continuation. Its deliver branch distinguishes an empty stack, a pending address and a saved numeric name. These operations use numeric data throughout; they do not decode Source values.

**Definition 1.2 (Numeric first return).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.workspaceCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.workspaceCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A primitive-recursion program iterates the encoded numeric step. Minimization searches for the first instruction with the action tag, and the program returns that instruction's full action payload. Its equality with PFun.fix of numericTick follows from the universal raw-instruction realization and the conditional first-return theorem. No finite bound on workspace, stack, address or search index is introduced.

**Definition 1.3 (Closed original-state program).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.selectorCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.selectorCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input projection extracts the workspace from the nested product encoding of OriginalState. The program then applies workspaceCode. Common input, epoch and retained history remain outside this selector computation, as in sourceService. The program data contains constructors, composition, recursion, minimization and computable constants. It contains no classical choice or semantic sourceDecoder.

**Definition 1.4 (Existing bounded evaluation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.evaluate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The program is supplied directly to evalOriginalActionFromCode, which evaluates with magnitude and recursion fuel 2 raised to the supplied stage and decodes the full OriginalAction Nat. A missing bounded value is not evidence of divergence.

**Definition 1.5 (Existing controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.controller`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.controller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

originalNativeControlFromCode consumes exactly the same selectorCode. The original controller retains its state decoding, four reply continuations and acquired-history transitions. Its local events are evaluator work and do not identify the producer's local chronology.

**Theorem 1.6 (Universal raw instruction).**

$$\forall n: Nat, (\operatorname{eval}\left(tickCode, n\right) = \operatorname{some}\left(\operatorname{encode}\left(\operatorname{numericTick}\left(n\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.tick_code_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural workspace, tickCode evaluates to the complete encoded numericTick instruction. The finite scan invariant covers every raw list cell. Boolean-address checks and all address-valued frames exactly match recursive decoder definedness, and any successfully decoded NumericControl re-encodes to the original natural number. A failed decode therefore uses exactly numericInitial. Two reversals compute each appended child address. Visit constructs all four reply continuations; deliver handles an empty stack, a pending address and a saved name. The proof also accounts for the primitive-recursion branch evaluating its zero case before a positive case.

**Theorem 1.7 (Exact conditional first return).**

$$(\forall m: Nat, (\operatorname{eval}\left(tickCode, m\right) = \operatorname{some}\left(\operatorname{encode}\left(\operatorname{numericTick}\left(m\right)\right)\right))) \implies (\forall n: Nat, (\operatorname{eval}\left(workspaceCode, n\right) = \operatorname{map}\left(encode, \operatorname{selectWorkspace}\left(n\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.workspace_code_correct_of_tick` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that tickCode evaluates to the complete encoded numericTick instruction on every natural workspace. Then workspaceCode agrees with selectWorkspace, after encoding the returned action, on every natural workspace. This is equality of partial values, so it includes definedness. The proof computes quotient and parity exactly, identifies the minimization index with the first action, and directly uses Partrec.fix_aux to connect the numeric iterates to the existing first-return function. It introduces no state restriction, finite fuel premise or new source traversal.

**Definition 1.8 (Conditional original-state realization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.realizationOfTick`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.realizationOfTick` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given the same universal instruction premise, extract the workspace from the genuine OriginalState encoding and use the first-return law to build the existing OriginalCodeRealization sourceService with code exactly selectorCode. The universal tick_code_correct theorem supplies this premise; realization applies the builder to it. The existing original_code_service_simulation applies to the resulting record whenever the premise is supplied.

**Theorem 1.9 (Exact original-state equality).**

$$\forall s: OriginalState, (\operatorname{eval}\left(selectorCode, \operatorname{encode}\left(s\right)\right) = \operatorname{map}\left(encode, \operatorname{select}\left(sourceService, s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.selector_code_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every genuine OriginalState, evaluating selectorCode on its encoded state equals sourceService.select with its complete returned action encoded. Equality of partial values preserves both values and definedness, including divergence. The proof supplies tick_code_correct to realizationOfTick, which uses workspace_code_correct_of_tick and the existing first-return bridge. Common input, epoch, history, arbitrary numeric workspace, invalid encodings and all reply continuations retain their original domains.

**Definition 1.10 (Existing realization consumer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.realization`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.realization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record has code exactly selectorCode and realizes field selector_code_correct. It is directly admissible as the argument of the existing original_code_service_simulation. That theorem retains external reads and terminal observations after erasing evaluator steps; it does not identify evaluator microsteps with the producer chronology. No new traversal, controller or simulation is introduced.

The code data is computable and closed. The equations are unbounded semantic statements and supply no uniform running-time, memory or fuel bound. A bounded evaluation returning no value proves no divergence. No physical installation or Source-valued computational decoder follows.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.controller`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.evaluate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.realization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.realizationOfTick`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.selectorCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.selector_code_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.tickCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.tick_code_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.workspaceCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.workspace_code_correct_of_tick`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer](NativeEffectiveSourceProducer.md)
