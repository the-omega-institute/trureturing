# Flat Projector Dephasing

## Abstract

Canonical dephasing of flat rank-one projections for exhaustive root-cover consumers.

**Theorem 1.1 (Recover a dephased common-unbiased root from an actual projector).**

$$CanonicalFlatProjectorRoot.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/FlatProjectorDephasing.flat_rankOne_projector_has_canonical_dephased_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an existing IsNormalizedRankOneProjection P in dimension six with diagonal one-sixth, define u_i=6P_i0. The theorem proves u_0=1, every u_i has squared modulus one, reconstructs P_ij=u_i conjugate(u_j)/6, and translates the second-basis diagonal condition into squared modulus six for H-adjoint u. The proof reuses the existing rank-one compression law and introduces no second projector or basis carrier. Root isolation and interval-cover soundness remain separate obligations.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/FlatProjectorDephasing.flat_rankOne_projector_has_canonical_dephased_root`
- Dependency: [D5/S3/Quantum/Tomography/RankOneContextCommutator](RankOneContextCommutator.md)
