# The original GLOBAL contract, obstruction and attaining application

## Abstract

The original two-block obstruction and the exact stopped three-word application of the literal inverse.

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

This theorem proves the lower obstruction in the internal-even-support classification. The attaining application below combines the physical inverse and the exact paid-trace interface with this obstruction. The parity argument is elementary finite-field algebra; no literature novelty or priority claim is made.

For the attaining application retain m>=5, k=2m-2, T=k+1=2m-1, the entire phase group P=ZMod(T), and both original alphabets. Each H(v) is an even subset of the representative interval 2<=j<m. For actual INITIAL value v, phase -j and every inherited legal tail s<k, the immutable target is B(v) on H(v) and A(v) elsewhere; its initial-bottom label is arbitrary. The two supports are nonempty and unequal for the fee-three conclusion, and A(v)!=B(v) separately. Cross-value label coincidences are allowed.

Write mask(H,j) for the bit one on H and zero outside it, on all of P. Set q0(h)=mask(H(0),h), qz(h)=0 and q2(h)=mask(H(1),1+h), with phase arguments interpreted modulo T. The fixed stream has prefix prefixWord(m,q0), an all-zero m-bit word, prefixWord(m,q2), followed by all-zero words. Its nth word is indexed solely by the length of this execution's own chronological archive; neither the free value nor a reply selects a different stream. The prefixWord bit at position i is the parity of the row entries from zero through i, as defined in `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse`.

The two nonzero rows have even charge on offsets zero through m. Indeed translation permutes the full phase group, the sum of either support bit is its even cardinality modulo two, and every omitted offset has zero bit. Their endpoint charges are zero: the root endpoints are phases zero and m, while the third endpoints are one and m+1, all outside the corresponding support. The supplied short_window_charge_inverse therefore gives zero first and last literal bits for both words. The root clears every inherited tail, the zero wait is paid and clears its seam, and every subsequent crossed seam is safe. Every word is internally admissible because m<k. The conditions of safeRows and the incoming-root condition hold under both alphabets.

Apply actual_shared_charge_suffix to the same three rows and to each actual INITIAL record. Coprimality gcd(m,T)=1 admits every phase. The complete physical endpoints are some(v+a), some(v+a), some(v+a+b), where a=mask(H(0),j) and b=mask(H(1),j), so no legal initial source rejects. At the third index j-2m=j-1 modulo T, since 2m=1 modulo T. The windowCharge guard is retained: if j belongs to H(1), the representative of j-1 is between one and m-2 and hence lies in the guarded range; otherwise the shifted row is zero even if that guard excludes the argument. Thus the third difference is b rather than an unshifted root charge.

A finite fibre decoder receives only the actual root difference d. It returns some(0) if every p in P with mask(H(0),p)=d has mask(H(1),p)=0, otherwise some(1) if every such p has bit one, and otherwise none. The fibre is over all of P, including outside phases. An actually reached fibre is nonempty because it contains its INITIAL j. Consequently a returned bit is the constant target bit on that fibre, and none is equivalent to nonconstancy there. This uses equality of bits only, with no equality decision on the label type.

The stop function saves the INITIAL free value. Initial bottom returns its bottom label before any word. For a live value-zero source it issues the root, then returns B(0) on difference one and A(0) on zero. A live value-one source issues that same root and stops after it precisely when the fibre decoder returns a constant, returning the corresponding A(1) or B(1). A mixed fibre continues after the root and again after the paid zero wait. Only after issuing the third word does it use its own third difference to return B(1) on one and A(1) on zero. Later scalar values never replace the saved INITIAL value. The total stop function continues on other unmatched live archive patterns; they are not reached by these legal sources.

Let c(v,j) be one for value zero, one for a value-one phase whose root fibre is constant, and three otherwise. The actual emitted archive is exactly scriptArchive of the first c(v,j) words of the fixed three-word prefix, started at (v,-j,s). Its length is c(v,j), its PaidTrace returns the INITIAL target, and its own endpointDifferences are exactly the first c(v,j) entries of [some(a),some(0),some(b)]. For c=1 this statement includes only the executed root; no third endpoint is supplied to the stopping rule. For c=3 the zero word is a separate paid entry and gives no additional distinction. The exact native execution and fee follow by directly applying native_execute_paid_trace from `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace` to this stopped archive, without replacing it by an unstopped script.

The original scanner and integer-weight execution agree with the native record by output_record, execute_same and record_history in `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge`. The actual-source equivalence in whole_first_zero_acquisition identifies every AllowedBlock history with its joint INITIAL record, including initial bottom. Transporting the stopped trace through these equalities proves correctness for every original history. OriginalPresetFeasible with budget three uses exactly the stream and stop function just specified. Every selected complete word is paid and respects either original alphabet, and the target remains independent of the inherited tail.

If every reached root fibre were constant for value one, this very controller would return on every live source after one word, and on initial bottom after zero. The same stopped-trace argument would then make it OriginalPresetFeasible with budget two, contradicting original_global_two_block_obstruction. Hence some actual phase j has a mixed value-one root fibre. With value one and tail zero, SourceRecord holds at that phase because gcd(m,T)=1. The actual-source equivalence supplies an original AllowedBlock history with precisely that INITIAL record. Its execution of the same named controller pays three, establishing actual worst fee three rather than an unused horizon of three. The zero wait retains the mixed fibre because its endpoint repeats the root endpoint.

For m=5, H(0)={2,3} and H(1)={3,4}, the literal prefix is 00100|00000|00100; both value-one root fibres are mixed and pay three. For m=6, H(0)={2,3} and H(1)={4,5}, it is 001000|000000|000100. Its value-one root-one fibre is constant zero and stops after one word; the root-zero fibre is mixed and pays three. The third word 000100 differs from the independently usable unshifted H(1) root word 000010. Replacing the latter support by {2,3,4,5} makes the value-one root-one fibre constant one, still stopping after one word. The worst emitted-bit fees are fifteen and eighteen respectively, because each of the three paid words has m bits. All these statements retain every inherited legal tail, both alphabets and arbitrary separately distinct labels.

This application concerns only the nonempty unequal internal even-support family with k=2m-2. It does not settle empty or equal support branches, odd supports, tail-sensitive targets, other reader parameters or the general original acquisition objective. The construction and consequences are applications of the cited physical and execution interfaces; no literature-priority assertion is made.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.OriginalPresetFeasible`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.original_global_two_block_obstruction`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.presetSelector`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhysicalWindowDecoder](PhysicalWindowDecoder.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalAcquiredTrace](OriginalAcquiredTrace.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalExecutionBridge](OriginalExecutionBridge.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse](WindowChargeInverse.md)
