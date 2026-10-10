# The original GLOBAL contract and a two-block obstruction

## Abstract

One original preset stream cannot acquire unequal nonempty even interior supports in two blocks.

**Definition 1.1 (One literal stream with local stopping).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.presetSelector`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.presetSelector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A stop function receives only the free initial output and this source's chronological archive. If it returns no label, the selector emits the next word of one fixed stream, indexed by the number of blocks actually emitted. Every still-running archive in both free-value fibres uses that same stream.

**Definition 1.2 (Correct bounded execution on all actual INITIAL histories).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.OriginalPresetFeasible`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.OriginalPresetFeasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Feasibility supplies a stream and stop function whose selected words respect the chosen original alphabet. Initial bottom returns its fixed target label freely. For every actual finite AllowedBlock history, the original scanner and execute recursion must return the target of that history's immutable INITIAL record with fee at most the given budget. Full blocks, including rejection blocks, are charged. The controller receives no original history length, phase, inherited tail or interior observation.

**Theorem 1.3 (Unequal even interior supports require more than two blocks).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.original_global_two_block_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.original_global_two_block_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, put k=2m-2 and take the full phase group ZMod(k+1). Define j=-theta_INITIAL modulo k+1, using the standard representative 0 through k, where theta_INITIAL is the INITIAL record phase. In each free-value fibre choose a nonempty even support H(v) in this j coordinate, contained in the representative interval 2 through m-1, with the two supports unequal. Choose arbitrary labels A(v) and B(v), unequal separately in each fibre, and any immutable target such that, for every inherited tail 0<=s<k, its live value at the INITIAL record (v,-j,s) is B(v) when j belongs to H(v) and A(v) otherwise. Under either original alphabet this target has no feasible GLOBAL execution with budget two. Cross-value label coincidences and the bottom label are unrestricted.

The native bridge compares two actual INITIAL sources with equal free value and tail zero. Equality of both scheduled literal charges makes their acquired archives equal at every actually executed step. A stop at the root or after the first word therefore returns the same label; if they continue, rejection is simultaneous because legality depends only on the common tail and literal bits. The second charge is a mathematical function of the preset word. It does not supply an observation to a source that has stopped.

Every second literal charge has zero total parity and vanishes on the interior support interval 2 through m-1 in the same negative INITIAL-phase coordinate j=-theta_INITIAL modulo k+1. An even target mask constant on the two response cells with second charge zero is either zero or one canonical mask. Applying this normal form to both value fibres forces one support empty or the supports equal, contradicting the hypotheses.

This proves the lower obstruction in the internal-even-support classification. It does not construct a three-block stream, prove its upper bound, or claim the full zero/one/three classification. The parity argument is elementary finite-field algebra; no literature novelty or priority claim is made.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.OriginalPresetFeasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.original_global_two_block_obstruction`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.presetSelector`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder](PhysicalWindowDecoder.md)
