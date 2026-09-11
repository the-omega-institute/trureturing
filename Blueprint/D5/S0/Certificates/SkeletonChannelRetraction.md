# Sample-Preserving Channel Retraction

## Abstract

Fixed terminal observations admit an explicit output retraction without increasing the original canonical state budget.

**Definition 1.1 (mapChannels).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.mapChannels`

*Formalization.* `D5/S0/Certificates/SkeletonChannelRetraction.mapChannels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Postcompose the two terminal channels; retain the complete transition data.

**Definition 1.2 (channelMap).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.channelMap`

*Formalization.* `D5/S0/Certificates/SkeletonChannelRetraction.channelMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select the postcomposition associated with the original terminal channel.

**Theorem 1.3 (evalFrom_mapChannels).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.evalFrom_mapChannels`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.evalFrom_mapChannels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact evaluation commutes with channelwise postcomposition, including none.

**Theorem 1.4 (eval_mapChannels).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.eval_mapChannels`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.eval_mapChannels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start-state version for the existing block-code input representation.

**Definition 1.5 (signatureMap).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.signatureMap`

*Formalization.* `D5/S0/Certificates/SkeletonChannelRetraction.signatureMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every old used signature maps to a used signature with the same return.

**Theorem 1.6 (signatureMap_surjective).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.signatureMap_surjective`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.signatureMap_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Output retraction creates no signature outside the image of old ones.

**Theorem 1.7 (canonical_state_card_mapChannels_le).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.canonical_state_card_mapChannels_le`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.canonical_state_card_mapChannels_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Canonical state cost cannot increase under either terminal retraction.

**Theorem 1.8 (fixed_observation_preserved).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.fixed_observation_preserved`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.fixed_observation_preserved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed observed labels survive even when unobserved outputs change.

**Definition 1.9 (recurrentRetract).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.recurrentRetract`

*Formalization.* `D5/S0/Certificates/SkeletonChannelRetraction.recurrentRetract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In radix four, recurrent output two may be retracted to zero.

**Definition 1.10 (transientRetract).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.transientRetract`

*Formalization.* `D5/S0/Certificates/SkeletonChannelRetraction.transientRetract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In radix four, transient output zero may be retracted to one.

**Theorem 1.11 (recurrentRetract_ne_two).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.recurrentRetract_ne_two`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.recurrentRetract_ne_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrent retraction has precisely the intended forbidden-value exclusion.

**Theorem 1.12 (transientRetract_ne_zero).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.transientRetract_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.transientRetract_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transient retraction excludes zero without altering any other label.

**Definition 1.13 (NormalRange).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.NormalRange`

*Formalization.* `D5/S0/Certificates/SkeletonChannelRetraction.NormalRange` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite-state candidates with the reduced terminal alphabets.

**Theorem 1.14 (retracted_normalRange).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.retracted_normalRange`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.retracted_normalRange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit retraction constructs that range for every partial skeleton.

**Theorem 1.15 (normalized_sample_feasibility_iff).**

Lean statement: `D5/S0/Certificates/SkeletonChannelRetraction.normalized_sample_feasibility_iff`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonChannelRetraction.normalized_sample_feasibility_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduced-output search is equisatisfiable at the same canonical budget. Only the given observations are assumed to avoid the two forbidden labels; the unknown original machine's unobserved outputs are unrestricted.

## References

- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.NormalRange`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.canonical_state_card_mapChannels_le`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.channelMap`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.evalFrom_mapChannels`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.eval_mapChannels`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.fixed_observation_preserved`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.mapChannels`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.normalized_sample_feasibility_iff`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.recurrentRetract`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.recurrentRetract_ne_two`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.retracted_normalRange`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.signatureMap`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.signatureMap_surjective`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.transientRetract`
- Truth anchor: `D5/S0/Certificates/SkeletonChannelRetraction.transientRetract_ne_zero`
- Dependency: [D5/S0/Automata/BinaryZeckendorfBlockSkeleton](../Automata/BinaryZeckendorfBlockSkeleton.md)
