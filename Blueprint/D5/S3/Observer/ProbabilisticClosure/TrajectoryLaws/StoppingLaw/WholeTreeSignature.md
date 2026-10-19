# Whole-tree oriented signatures and paid execution

## Abstract

Whole-tree oriented signatures and paid execution

A read position is a finite ordered list of Boolean branch choices. The parity skeleton retains every terminal label, branch and address parity. In each phase, the signature records equality and inequality among the target spin index and the minus and plus spin indices of every potential read occurrence. Missing and inactive positions repeat the target index, so they add no equality information.

**Theorem 1.1 (Positions in the parity skeleton).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_skeleton`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_skeleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tree and position, the address in the parity skeleton is the original address reduced modulo two, when that position is a read node.

**Theorem 1.2 (Relabeling preserves height).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.relabel_height`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.relabel_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer address map preserves tree height on every formal branch.

**Theorem 1.3 (Potential address image).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.relabel_addresses`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.relabel_addresses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite set of addresses after relabeling is exactly the image of the original set.

**Theorem 1.4 (Relabeling at an occurrence).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every ordered position, address lookup commutes with the integer address map.

**Theorem 1.5 (Occurrence addresses are potential addresses).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_in_addresses`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_in_addresses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every successful address lookup belongs to the tree address set.

**Theorem 1.6 (Distinct addresses and read occurrences).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addresses_card_le_readCount`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addresses_card_le_readCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of distinct potential addresses is at most the number of potential read occurrences. Repeated addresses and mutually exclusive branches remain distinct occurrences in the latter count.

**Theorem 1.7 (Binary-tree occurrence bound).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.readCount_height_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.readCount_height_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tree, its potential read count plus one is at most two raised to its height.

**Theorem 1.8 (Parity-preserving relabeling).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.skeleton_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.skeleton_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A map preserving parity at every potential address leaves the complete ordered parity skeleton unchanged.

**Theorem 1.9 (Signature invariance of the full observation law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.same_signature_observation_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.same_signature_observation_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean target j, pair of read trees with the same signature, and permitted Bias, the original source pushforward laws agree. The observation includes the actual hidden target, optional output, return indicator and paid depth. The proof transports spin assignments phase by phase and then proves execution commutation by recursion over the common ordered skeleton. Nonreturn leaves retain their exact paid depth; repeated and separator calls remain charged.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_in_addresses`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_relabel`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addressAt_skeleton`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.addresses_card_le_readCount`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.readCount_height_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.relabel_addresses`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.relabel_height`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.same_signature_observation_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.skeleton_relabel`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/FiniteCore](FiniteCore.md)
