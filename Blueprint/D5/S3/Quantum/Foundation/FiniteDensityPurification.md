# Finite Density Purification

## Abstract

A finite density state has a canonical normalized purification with exact reduced marginal.

**Definition 1.1 (Canonical purification with exact marginal and matrix).**

$$\psi=\operatorname{purify}(\operatorname{toMState}(\rho)), \operatorname{marginalRight}(\operatorname{toDensity}(\operatorname{pure}(\psi)))=\rho.$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteDensityPurification.purification` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg; Leonardo A. Lessa; Rodolfo Soldati (2026). *Finite density states and strong subadditivity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/2725b6f621901d4cd330869e9b77105045c1582e/QuantumInfo/Entropy/SSA.lean>.

*Commentary.*

For a density state ρ on a finite index type a with DecidableEq, purification returns the normalized ket ψ = MState.purify (toMState ρ) on a × a, bundled with marginalRight (toDensity (MState.pure ψ)) = ρ. The same-matrix conversion toMState uses the shared supplier carrier; toDensity returns to the project's canonical density states.

The returned subtype also certifies CStarMatrix.ofMatrix.symm (toDensity (MState.pure ψ)).1 = Matrix.vecMulVec ψ (fun i => star (ψ i)). Normalization is part of Ket. Singular states are included: the construction imposes no invertibility hypothesis.

This is the project's DensityState construction using the attributed Physlib MState.purify and MState.purify_spec from States/Mixed/MState at immutable revision 2725b6f621901d4cd330869e9b77105045c1582e. The supplier theorem states (MState.pure σ.purify).traceRight = σ for MState σ; the project construction transports that identity to marginalRight. The original copyright and Apache-2.0 notices remain in the consumed Lean sources.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteDensityPurification.purification`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
