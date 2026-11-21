# A common sequence for both forward deficits

## Abstract

One sequence of faithful three-qubit pairs gives a log 2 gap in both forward deficits for every fixed positive geodesic parameter.

Theorem 10.16 already rules out a trace-distance modulus at fixed B by relabeling the balanced classical label as C and adjoining an independent faithful B using Proposition 4.3. In that reduction the AC marginal carries the varying signal and label. The construction here keeps AC and BC fixed and matches AB within each pair.

**Theorem 1.1 (Regularization on compact parameter sets).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence.eventually_uniform_regularization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence.eventually_uniform_regularization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

For fixed 0 < u < 1/2, joint continuity of the spectral quadratic form in t and the regularization parameter gives a single right neighborhood of zero for each compact subset of 0 < t < 1 and each positive error tolerance. The spectrum of the first matrix stays on a compact real interval, so both positive matrix powers have the continuous functional calculus needed at the singular boundary.

**Theorem 1.2 (One sequence for every fixed 0 < t ≤ 1).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Acknowledgement.* Andris Ambainis; Michele Mosca; Alain Tapp; Ronald de Wolf (2000). *Private Quantum Channels*. DOI: [10.1109/SFCS.2000.892142](https://doi.org/10.1109/SFCS.2000.892142).

*Acknowledgement.* Andreas Bluhm; Ángela Capel; Paul Gondolf; Antonio Pérez-Hernández (2023). *Continuity of Quantum Entropic Quantities via Almost Convexity*. DOI: [10.1109/TIT.2023.3277892](https://doi.org/10.1109/TIT.2023.3277892). URL: <https://arxiv.org/pdf/2208.00922v3#page=27>.

*Commentary.*

There is one sequence of faithful three-qubit pairs. Within each pair the AB, AC and BC marginals agree. For both states at every index B is I/2 and AC and BC are I/4. The shared AB marginal varies with the index. The trace distance tends to zero from above. For every fixed 0 < t ≤ 1 both signed forward gaps converge to log 2, with one-sided reference I/2 and the actual C marginal in the two-sided deficit. The proof uses u_n = 1/(n+3), controls the error within u_n on [u_n, 1−u_n], and also enforces the error bound at t = 1. Every fixed interior t eventually lies in these intervals.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence.eventually_uniform_regularization`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence.result`
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI](CapelCostaRicoForwardGeodesicCMI.md)
