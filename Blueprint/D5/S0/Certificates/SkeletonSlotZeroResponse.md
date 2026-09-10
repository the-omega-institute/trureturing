# Shared Zero Responses of Slot Skeletons

## Abstract

Every slot candidate has a shared-zero response factorization and exact recurrent-capacity rank constraints.

**Definition 1.1 (Advance).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.advance`

*Formalization.* `D5/S0/Certificates/SkeletonSlotZeroResponse.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuse the single zero transition of the existing serialization.

**Theorem 1.2 (Advance add).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.advance_add`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotZeroResponse.advance_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All zero lengths are iterates of the same map.

**Theorem 1.3 (Evalfrom zero prefix).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.evalFrom_zero_prefix`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotZeroResponse.evalFrom_zero_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arbitrary number of zero blocks can be removed using the original Option-valued evaluation, including every possible continuation.

**Definition 1.4 (Gapslot).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.gapSlot`

*Formalization.* `D5/S0/Certificates/SkeletonSlotZeroResponse.gapSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After entering a transient slot, k+1 zeroes followed by one select this slot. Different k use the same zeroTarget, slotOf and returnTarget.

**Theorem 1.5 (Evalfrom one zero gap).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.evalFrom_one_zero_gap`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotZeroResponse.evalFrom_one_zero_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared-gap factorization is tied to existing block evaluation.

**Definition 1.6 (Probe).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.probe`

*Formalization.* `D5/S0/Certificates/SkeletonSlotZeroResponse.probe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact one-hot readout of either a digit or a selected transient slot. The latter is a latent structural readout, not a supplied arithmetic oracle.

**Definition 1.7 (Response).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.response`

*Formalization.* `D5/S0/Certificates/SkeletonSlotZeroResponse.response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sampled joint zero responses with arbitrary row access states and delays.

**Definition 1.8 (Reach).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.reach`

*Formalization.* `D5/S0/Certificates/SkeletonSlotZeroResponse.reach` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One-hot intermediate recurrent states.

**Definition 1.9 (Readout).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.readout`

*Formalization.* `D5/S0/Certificates/SkeletonSlotZeroResponse.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuation response of each recurrent state.

**Theorem 1.10 (Response factorization).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.response_factorization`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotZeroResponse.response_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sampled joint response factors through the actual recurrent carrier. No reachability, state ordering or self-loop restriction is imposed.

**Theorem 1.11 (Response rank le).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.response_rank_le`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotZeroResponse.response_rank_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every candidate supplies a completion whose response rank is at most r.

**Theorem 1.12 (Response det eq zero).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.response_det_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotZeroResponse.response_det_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every square response minor larger than the recurrent capacity vanishes.

**Theorem 1.13 (Capacity ge of right inverse).**

Lean statement: `D5/S0/Certificates/SkeletonSlotZeroResponse.capacity_ge_of_right_inverse`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonSlotZeroResponse.capacity_ge_of_right_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A supplied right inverse is an exact finite lower-bound certificate for this response, requiring neither numerical rank thresholds nor determinants.

## References

- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.advance`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.advance_add`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.capacity_ge_of_right_inverse`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.evalFrom_one_zero_gap`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.evalFrom_zero_prefix`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.gapSlot`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.probe`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.reach`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.readout`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.response`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.response_det_eq_zero`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.response_factorization`
- Truth anchor: `D5/S0/Certificates/SkeletonSlotZeroResponse.response_rank_le`
- Dependency: [D5/S0/Certificates/SkeletonSlotCNF](SkeletonSlotCNF.md)
