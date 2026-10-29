# Normalized two-input twisted coefficients in the actual fixed restricted dual

## Abstract

Normalized two-input twisted coefficients in the actual fixed restricted dual

Both inputs belong to the negative eigenspace of the original actualParity on ActualTensor D hu. At rank twenty-four this is the integer conformal sector, beginning at weight two. The ground has positive actualParity and is excluded. The target is the direct sum, over all integer source weights, of the full algebraic duals of grade D d intersect fixedSpace D. No identification of this target with the original fixed source is assumed.

The standard mode I_m is the coefficient of z^(-m-1). For weights H and K, its pairing with a fixed source a is the finite sum over p<K-1 and q<H-1 of (-1)^(H+s)/(p!q!) times actualForm(L1^p v, C_a[2s] L1^q u), where s=m+1-p-2H+q. The original right orientation K_R is used; the selected ground pairing is unchanged and symmetry is not assumed. Finite extension uses the existing actualAmbientBasis, followed by restriction of both inputs to the original negative parity eigenspace.

The original rank/16 zero mode and the actual Virasoro bracket lower odd oscillator degree by two under L1. Negative odd degrees have no nonzero eigenvectors in the original tensor basis. These facts justify the finite homogeneous L1 cutoffs. The existing signed corrected-field output law and actualForm odd-grade orthogonality select the source weight H+K-m-1 for every fixed-grade test vector. Positive Gram then supplies a finite standard-mode upper bound for every pair of actual vectors.

The carrier and parity conventions are those of Frenkel, Lepowsky and Meurman, PNAS 81 (1984), pp.3257--3258, equation (5). The finite kernel construction and its proof terms are repository work, with no claim that the announcement supplies a detailed proof of this formula. The sharp homogeneous cutoff is m>H+K-1. The finite opposite action on original grade e lands in grade e+m-d+1; its dual pullback sends grade E to E+d-m-1. The full signed mixed Jacobi identity, the nonzero vacuum channel, and consumption on the actual Leech data remain unfinished. No complete intertwiner, orbifold gluing, three-twisted crossing, Monster action, full CFT, string theory or AdS/CFT result is asserted.

All-vector input translation on this same normalized coefficient is proved in MixedTranslation: I_m(L(-1)u)v equals -m I_(m-1)(u)v. The translation proof uses the original rank/16 stress and selected form, with no symmetry premise.

**Theorem 1.1 (Pairing with every actual fixed-grade test vector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite original-basis extension, target L1 weight lowering and the existing ordered form orthogonality identify every homogeneous coefficient with the finite normalized double sum, including all excluded source grades.

**Theorem 1.2 (All-vector standard-mode truncation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive original source energy and the finite supports of both actual tensor vectors give an explicit upper cutoff for standard modes. This coarse all-vector bound is separate from the sharp homogeneous bound.

**Theorem 1.3 (Sharp homogeneous standard-mode cutoff).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_homogeneous_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_homogeneous_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient lies in the actual fixed-source dual grade H+K-m-1. Negative source grades vanish under positive Gram, giving the exact homogeneous cutoff.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_homogeneous_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_pairing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner.normalizedCoefficient_truncation`
- Dependency: [D5/S3/VertexAlgebra/CorrectedInversion/Dual](../CorrectedInversion/Dual.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockParityField](../HalfFock/LatticeHalfFockParityField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualEnergyRestrictedDual](ActualEnergyRestrictedDual.md)
