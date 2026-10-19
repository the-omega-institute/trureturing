# Authentic validation and the retained row

## Abstract

Complete selected rows at their actual successful guard validation.

The source register changes only by the fixed substitution. A guard address reaches an actual alpha or beta leaf. Existing subtree addresses survive substitution, and intrinsic depth increases by one at every update. The same leaf reply at the same address therefore cannot recur after a positive number of updates.

**Definition 1.1 (The complete byte row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.recordBytes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.recordBytes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root cut has the constant four-cell row. The child cut has a literal leaf row on a leaf source, or the two fully addressed holes followed by the equality bit and row terminator on a branch source. The equality bit retains both diagonal pairs and both off-diagonal memberships or nonmemberships.

**Definition 1.2 (Literal exterior and complete partition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.decodeRow`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.decodeRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoder checks the whole fixed-alphabet row and its selected cut. Valid rows decode to the literal exterior and full finite hole partition; all other rows are rejected. No absent operand is converted into a negative comparison.

**Definition 1.3 (The authentic guard source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Candidate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Candidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are an actual guard source V and a natural update count k with current source equal to the kth substitution iterate of V. The saved guard is an actual leaf reply in V. When k is zero, a finite update-free actual prefix leads from the fresh guard exit to the current candidate configuration. Positive k asserts no accuracy for the partly acquired candidate row. These objects occur only in the proof.

**Definition 1.4 (The actual successful validation event).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Captured`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Captured` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exist an earlier event v and its actual Work w. The schedule executes an observer step at v while the call is pending; its whole configuration is active with the same selected cut, control twenty five and the retained row. Reading the actual source at w's guard address returns w's saved guard reply. The row is exactly recordBytes for that same actual source and decodes to its complete literal record. At every later observer index before the stated boundary, the actual instruction is local or Return. Thus no later Read intervenes.

**Definition 1.5 (Body and cleanup conditions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Certified`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Certified` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Body phases retain an authentic candidate. Cleanup and ready configurations retain the certificate of their actual successful validation. Guard search and reset use the reachable workspace conditions of the native scanner.

**Theorem 1.6 (Every ready row has an authentic complete capture).**

$$\forall u: \operatorname{Source}, (\forall s: \operatorname{Nat} \to \operatorname{Bool}, (\forall n: \operatorname{Nat}, (\forall q: \operatorname{Bool}, (\forall r: \operatorname{List}\left(\operatorname{Cell}\right), ((\operatorname{config}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right) = \operatorname{ready}\left(q, r\right)) \implies \operatorname{Captured}\left(u, s, n, q, r\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.returning_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source, active event schedule and finite prefix, reaching the whole ready configuration implies Captured. A successful validation forces the authentic guard epoch to be zero. The intervening actual body therefore has a stationary execution on the validation source. Determinism compares it with the actual stationary root, leaf or paired-subtree execution, including the full row and its partition sign. Cleanup preserves the row and performs only local instructions before the separate Return. Independent writer updates after validation do not alter the retained row's designated capture source.

**Definition 1.7 (Writer flags of the complete raw word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.eventSchedule`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.eventSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an index within the word, the schedule is true exactly for an independent update. Every observer event has false flag, and indices after the finite word also have false flag. The actual legal word retains every local step, Read and separate Return.

**Theorem 1.8 (Every legal returning raw history has its complete actual record).**

$$\forall u: \operatorname{Source}, (\forall h: \operatorname{Word}, (\forall q: \operatorname{Bool}, (\forall r: \operatorname{List}\left(\operatorname{Cell}\right), ((\operatorname{Run}\left(\operatorname{step}, \operatorname{entry}, u, h, \operatorname{ready}\left(q, r\right)\right)) \implies \operatorname{Captured}\left(u, \operatorname{eventSchedule}\left(h\right), \operatorname{length}\left(h\right), q, r\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.all_returning_histories` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal finite Run from entry to the whole ready row, Captured holds at the raw word's length under its own eventSchedule. Induction on the actual Run maps each independent write, local instruction, authentic Read and Return to exactly one trajectory event. The shifted-trajectory identity retains the actual intermediate world. The resulting certificate identifies the last successful validation Read in that same execution, and the complete literal record at its actual source.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Candidate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Captured`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.Certified`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.all_returning_histories`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.decodeRow`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.eventSchedule`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.recordBytes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness.returning_capture`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress](NativeSelectedRAProgress.md)
