# Prime Fourier-Magnus Commutator Bridge

## Abstract

The two-channel Fourier commutator is the second-Magnus swap kernel times the interpreted free-Lie bracket.

**Definition 1.1 (Matrix commutator).**

Lean statement: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.matrixCommutator`

*Formalization.* `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.matrixCommutator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The noncommutative curvature of two matrix channels is their ordered product difference.

**Definition 1.2 (Two-channel Fourier generator).**

Lean statement: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.twoChannelFourierGenerator`

*Formalization.* `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.twoChannelFourierGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two matrix channels are modulated by their unitary Fourier characters and added.

**Theorem 1.3 (Free-Lie pair maps to matrix commutator).**

Lean statement: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.free_lie_degree_two_matrix_lift`

*Formalization.* `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.free_lie_degree_two_matrix_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal degree-two event word is interpreted as the associative commutator of the two channel matrices.

**Theorem 1.4 (Exact two-channel Magnus factorization).**

Lean statement: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_factorization`

*Formalization.* `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-time commutator of the Fourier generator equals the frozen swap kernel times the channel commutator.

**Theorem 1.5 (Fourier kernel is the free-Lie coefficient).**

Lean statement: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_free_lie`

*Formalization.* `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_free_lie` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same factorization is expressed directly through the universal free-Lie degree-two word.

**Theorem 1.6 (Equal times erase the response).**

Lean statement: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_equal_time`

*Formalization.* `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_equal_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coincident time slots force the second-Magnus matrix commutator to vanish.

**Theorem 1.7 (Commuting channels erase the response).**

Lean statement: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_eq_zero_of_channels_commute`

*Formalization.* `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_eq_zero_of_channels_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the two channel matrices commute, every two-time Fourier-Magnus commutator vanishes.

## References

- Truth anchor: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.matrixCommutator`
- Truth anchor: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.twoChannelFourierGenerator`
- Truth anchor: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.free_lie_degree_two_matrix_lift`
- Truth anchor: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_factorization`
- Truth anchor: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_free_lie`
- Truth anchor: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_equal_time`
- Truth anchor: `D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge.two_channel_fourier_commutator_eq_zero_of_channels_commute`
- Dependency: [D5/S3/Observer/Chronology/StepTwoFreeLieBridge](StepTwoFreeLieBridge.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature](../AgencyHolonomy/SecondMagnusSwapCurvature.md)
