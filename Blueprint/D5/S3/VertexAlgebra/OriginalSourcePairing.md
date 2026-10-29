# Original integer-source bilinear pairing

## Abstract

This module constructs a complex bilinear BPZ-source form on the literal original lattice carrier.  For each oscillator frequency `k`, the scalar `integerScale k = (k+1)/(k+1/2)` retunes the existing signed polynomial Wick supplier to the integer current contraction.  The retuning is an algebra equivalence on the same `MvPolynomial (Fin D.rank × Nat) Complex` ring; no carrier replacement or Hermitian Riesz form is used.

The finite charge form is
`sourcePairing D v w = sum a, integerWick D (v a) (w (-a))`, with the existing finite-support charge sum.  The construction includes arbitrary finite rank, rank zero, indefinite integral symmetric even lattices, and uses `IsUnit D.G.det` only for both-sided nondegeneracy.

## Proved declarations

- `integerScale`, `integerScale_ne_zero`, and `integerScale_mul_frequency` establish the exact frequency retuning.
- `retuneMatrix`, `retuneInverseMatrix`, `retune`, `retune_X`, `retune_pderiv`, and `retune_annihilate` establish the two-sided substitution and its derivative bridge.
- `integerWick` reuses `SignedOscillatorWick.wick` on the same oscillator ring.
- `integerWick_creation` and `integerWick_lowering` prove the integer creation/lowering transpose with contraction `-(k+1)G`.
- `integerWick_symmetric` and `sourcePairing_symmetric` prove complex bilinear symmetry.
- `sourcePairing_vacuum` proves the literal vacuum normalization `B(vacuum,vacuum)=1`.
- `integerWick_nondegenerate` and `sourcePairing_nondegenerate` prove both-sided nondegeneracy under `IsUnit D.G.det`.
- `sourcePairing_single` and `sourcePairing_single_single` expose charge isolation and the exact opposite-charge coefficient formula.

The construction consumes the existing signed Wick, substitution, annihilation and finite-support APIs.  It does not claim the all-source `wordField` BPZ induction, charged-generator transpose, theta isometry, energy orthogonality, mixed Jacobi/translation, crossing, fusion, string consistency, or AdS/CFT completion.  Those remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalSourcePairing`
- Supplier: `D5/S3/VertexAlgebra/TwistedGround/SignedOscillatorWick`
- Substitution supplier: `D5/S3/VertexAlgebra/OriginalCurrentMetric`
