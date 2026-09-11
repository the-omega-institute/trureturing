# Golden Base-Four Joint Zero Response Certificate

## Abstract

An exact inverse certifies fourteen independent joint responses of the existing machine, with a fixed-profile scope distinct from powers-only minimality.

**Definition 1.1 (Recurrent).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.recurrent`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.recurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Embedding the previous-zero carrier into the existing full machine.

**Definition 1.2 (Transient).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.transient`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.transient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Embedding the seven transient slots into the existing full machine.

**Definition 1.3 (Zero).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.zero`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recurrent zero row of the already specified full table.

**Definition 1.4 (Select).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.select`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.select` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Slot requested by each recurrent one edge.

**Definition 1.5 (Returnto).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.returnTo`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.returnTo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Return target of each existing transient slot.

**Theorem 1.6 (Zero matches).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.zero_matches`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroResponse.zero_matches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed zero table is exactly the original machine's row.

**Theorem 1.7 (Select matches).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.select_matches`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroResponse.select_matches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selector table agrees with the original machine's one transitions.

**Theorem 1.8 (Return matches).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.return_matches`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroResponse.return_matches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The slot returns agree with the original machine's zero transitions.

**Definition 1.9 (Skeleton).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.skeleton`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.skeleton` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Original outputs are reused without a second digit oracle.

**Definition 1.10 (Slots).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.slots`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.slots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An explicit serialization in the existing slot witness type.

**Definition 1.11 (Origin).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.origin`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.origin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row origins: the initial state followed by named transient returns.

**Definition 1.12 (Rowdelay).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.rowDelay`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.rowDelay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Number of zeroes after the row origin.

**Definition 1.13 (Columndelay).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.columnDelay`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.columnDelay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Column zero depths; only depths zero through three are needed.

**Definition 1.14 (Test).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.test`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.test` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Joint probes distinguish output digits and selected transient slots.

**Theorem 1.15 (Access exhausts recurrent).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.access_exhausts_recurrent`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroResponse.access_exhausts_recurrent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every recurrent state has the recorded access by a transient return or start.

**Definition 1.16 (Profileminor).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.profileMinor`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.profileMinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This matrix is computed from the existing machine, not assumed data.

**Definition 1.17 (Profileinverse).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.profileInverse`

*Formalization.* `D5/S1/Digit/GoldenBase4ZeroResponse.profileInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An exact integer-valued right inverse; no approximate rank is used.

**Theorem 1.18 (Profile inverse certificate).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.profile_inverse_certificate`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroResponse.profile_inverse_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite rational calculation certifies the whole matrix product.

**Theorem 1.19 (Profile rank fourteen).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.profile_rank_fourteen`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroResponse.profile_rank_fourteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fourteen independent responses are forced for this labelled profile.

**Theorem 1.20 (Same profile recurrent lower bound).**

Lean statement: `D5/S1/Digit/GoldenBase4ZeroResponse.same_profile_recurrent_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4ZeroResponse.same_profile_recurrent_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any deterministic slot realization of the same labelled profile requires at least fourteen recurrent states. This premise is stronger than fitting powers.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.access_exhausts_recurrent`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.columnDelay`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.origin`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.profileInverse`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.profileMinor`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.profile_inverse_certificate`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.profile_rank_fourteen`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.recurrent`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.returnTo`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.return_matches`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.rowDelay`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.same_profile_recurrent_lower_bound`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.select`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.select_matches`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.skeleton`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.slots`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.test`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.transient`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.zero`
- Truth anchor: `D5/S1/Digit/GoldenBase4ZeroResponse.zero_matches`
- Dependency: [D5/S0/Certificates/SkeletonSlotZeroResponse](../../S0/Certificates/SkeletonSlotZeroResponse.md)
- Dependency: [D5/S1/Digit/GoldenBase4IntervalMachine](GoldenBase4IntervalMachine.md)
