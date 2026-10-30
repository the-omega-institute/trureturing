# Finite skew exchange on the original fixed source

## Abstract

Finite skew exchange on the original fixed source

D is the original symmetric even integral lattice datum, hu is a unit integer determinant, hD is positive definiteness of the real Gram matrix, and h24 is rank twenty-four. Both inputs range over the complete negative eigenspace of the original actualParity on the original ActualTensor. The output is the original theta-fixed Carrier, and m is every signed integer standard mode.

sourcePairingDualEquiv is the concrete sourcePairing-induced equivalence E from the original fixed carrier to MixedIntertwiner.FixedRestrictedDual. It directly consumes FixedGradedDuality.fixedRestrictedDualEquiv, sourcePairing_nondegenerate, sourcePairing_theta and sourcePairing_grade. The grade projection commutes with theta by the original internal grade decomposition; the only dual reindexing reverses the order of the grade and fixed subtypes. Its evaluation is literally (E x d) a = sourcePairing D x.val a.val. originalCoefficient D hu hD m u v is E.symm applied to the original normalizedCoefficient D hu m u v.

**Theorem 1.1 (All-input original-source finite skew).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceSkew.originalCoefficient_skew`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceSkew.originalCoefficient_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D, hu, hD, h24 as above, every integer m and arbitrary original negative-parity u,v, the j-family ((-1)^(m+j+1)/j!) smul fixedTranslation(D)^j(originalCoefficient D hu hD (m+j) v u) has finite support on the original fixed carrier. originalCoefficient D hu hD m u v equals its finsum over natural j. The sign uses complex integer zpow, j is cast to the integers in each mode, and j! is cast to the complex numbers before division.

For actual homogeneous input weights H,K and test grade d=H+K-m-1, each original normalizedCoefficient_pairing summand with s=m+1-p-2H+q is transposed once. actualForm_symmetric applies to the unchanged selected actualForm, without a new target premise. MixedJacobi.actual_homogeneous_transpose changes the corrected mode 2s to -2s-4d+2j=2t, with t=m+j+1-q-2K+p. The original factorial indices merely swap. The sign identity compares H+s+d with m+j+1+K+t modulo two, for arbitrary signed m,d. All sums are finite before their order is exchanged. Off-grade evaluations vanish using the original homogeneous coefficient support.

The source transpose is first cut at R_a=a.val.support.sup(fun c => weightedTotalDegree(sourceWeight D)(a.val c))+1. The actual source Sugawara nilpotence theorem kills every later term. Finite expansions in actualAmbientBasis extend the identity to arbitrary inputs; negative_support and basis_parity retain precisely the original negative sector, and actual_basis_eigenvalue supplies each supported integer weight. The same test-vector cutoff R_a is used throughout this extension.

The literal source stress adjunction sourcePairing(D,L(-1)x,a)=sourcePairing(D,x,L1 a) specializes sourcePairing_allState to the actual grade-two conformal omega at mode zero. Existing conformal-polynomial homogeneity and lowering identify its grade and kill L1 omega, so higher source BPZ terms vanish. omega_modes and sugawaraMode_minus_one_eq_translation identify the two surviving literal operators. Finite induction transports every power of fixedTranslation against the matching source L1 power.

Before mapping the vector finsum, normalizedCoefficient_truncation in swapped order v,u bounds its support by range J, where B0=maxOddWeight(D,hu,u.val)+maxOddWeight(D,hu,v.val)+3 and J=(B0+1-m).toNat. Evaluation compares this vector cutoff with R_a by padding both to their maximum. Source nilpotence and coefficient truncation kill the respective tails; no infinite sum exchange is used.

This is classical contragredient and skew calculus, using the established lattice and twisted-sector constructions and their existing attributions; no literature novelty is asserted. The proof does not assume or invoke a full extension VOA or StateField.skew_symmetry. Three-twisted crossing, a complete extension, Monster identification, CFT sewing, fusion and anomalies, string theory and AdS/CFT remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceSkew.originalCoefficient_skew`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedGradedDuality](../Lattice/FixedGradedDuality.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/AllStateTranspose](../SourceBPZ/AllStateTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry](ActualPairingSymmetry.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedJacobi](MixedJacobi.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedOpposite](MixedOpposite.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedTranslation](MixedTranslation.md)
