# Finite Density Purification

## Abstract

A finite density state has a canonical normalized purification with exact reduced marginal.

**Theorem 1.1 (Canonical purification has the exact marginal).**

$$\operatorname{traceRight}(\operatorname{pure}(\operatorname{purify}(rho)))=rho.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/FiniteDensityPurification.purify_spec` (`✓ std3`). ∎

*Citation.* Samuel L. Braunstein and Arun K. Pati (2007). *Quantum Information Cannot Be Completely Hidden in Correlations: Implications for the Black-Hole Information Paradox*. DOI: [10.1103/PhysRevLett.98.080502](https://doi.org/10.1103/PhysRevLett.98.080502).

*Commentary.*

For a finite density state ρ on d, purify constructs the canonical ket on d × d from the spectral data of ρ; pure forms its rank-one state and tracing out the purifying factor returns exactly ρ.

The ket is normalized by the finite spectral decomposition, and the source retains Fintype and DecidableEq assumptions where required. This records the exact marginal identity only; it does not add a new Lean wrapper.

The declaration is reused from the selected upstream Physlib provenance at immutable revision 6a09b2d1761a0d4430083045a247eb121d8da260.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDensityPurification.purify_spec`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
