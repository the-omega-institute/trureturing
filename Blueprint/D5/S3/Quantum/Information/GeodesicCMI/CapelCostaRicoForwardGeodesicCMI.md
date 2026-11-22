# Forward geodesic CMI at one fixed parameter

## Abstract

At each fixed positive geodesic parameter, both forward deficits have a log 2 gap for faithful pairs that share every two-body marginal and approach each other.

**Definition 1.1 (One-sided forward deficit).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.oneSidedCMI`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.oneSidedCMI` (`✓ std3`).

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

In equation (357) the fine divergence runs from the joint state to its AB marginal tensored with the chosen C reference. The reduced term runs from the actual BC marginal to the B marginal tensored with the same reference.

**Definition 1.2 (Two-sided forward deficit).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.twoSidedCMI`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.twoSidedCMI` (`✓ std3`).

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Equation (357) uses the C marginal of the input state as the reference for the one-sided formula. On this witness family the C marginal is I/2, which agrees with the chosen one-sided reference.

**Definition 1.3 (Signed gap limits).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.ForwardGap`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.ForwardGap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

For the given sequence of matched faithful pairs, both differences take the first state's deficit minus the second's. Both differences converge to the natural logarithm of two.

**Theorem 1.4 (Regularization at fixed reference).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.regularization_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.regularization_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

At fixed u and fixed 0 < t ≤ 1, continuity on the positive semidefinite cone gives convergence to the unsmoothed value log 2 as η decreases to zero.

**Theorem 1.5 (Faithful pairs for a fixed parameter).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.exists_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.exists_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Acknowledgement.* Andris Ambainis; Michele Mosca; Alain Tapp; Ronald de Wolf (2000). *Private Quantum Channels*. DOI: [10.1109/SFCS.2000.892142](https://doi.org/10.1109/SFCS.2000.892142).

*Acknowledgement.* Andreas Bluhm; Ángela Capel; Paul Gondolf; Antonio Pérez-Hernández (2023). *Continuity of Quantum Entropic Quantities via Almost Convexity*. DOI: [10.1109/TIT.2023.3277892](https://doi.org/10.1109/TIT.2023.3277892). URL: <https://arxiv.org/pdf/2208.00922v3#page=27>.

*Commentary.*

For every fixed 0 < t ≤ 1, choose u_n = 1/(n+3) and select a positive regularization at each index using the fixed-reference limit. Both faithful states share their AB marginal within each pair. Their B is I/2 and their AC and BC are I/4 throughout the sequence. The trace distance tends to zero from above. The two coarse terms vanish and both fine comparisons use S_u, which gives zero on the reference arm. This theorem makes the sequence choice after fixing t.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.ForwardGap`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.exists_pointwise`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.oneSidedCMI`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.regularization_tendsto`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.twoSidedCMI`
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary](CapelCostaRicoForwardGeodesicBoundary.md)
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity](CapelCostaRicoGeodesicContinuity.md)
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI](CapelCostaRicoReverseGeodesicCMI.md)
