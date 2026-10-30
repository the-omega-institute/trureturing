# Input translation of the actual normalized two-twisted-input field

## Abstract

Input translation of the actual normalized two-twisted-input field

The input and output carriers and normalized coefficients are those of MixedIntertwiner. The translation map is the zero standard mode of the actual corrected conformal field on the negative actualParity sector. Its value is the original tensor stress L(-1), with the original rank/16 zero mode and unchanged selected bilinear form.

Corrected single-source inversion applied to the actual conformal polynomial supplies the stress transpose. The polynomial has weight two and is killed by the original source L1; all positive terms of the finite inversion sum vanish. The full existing twisted Borcherds law at zero source mode, combined with original source translation, supplies the actual stress-field commutator. Neither step assumes symmetry of the selected ground form.

The homogeneous coefficient proof uses the Virasoro relation for L1 powers applied to L(-1)u. The normalized term at q=0 and its successor recurrence are summed on explicit finite rectangles. The literal changes of index are p to p+1 and q to q-1. Boundary terms at p=K-1 and q=H-1 vanish by actual L1 nilpotence. The remaining scalar coefficient is -m. Finite expansion in the original actualAmbientBasis extends the result to every negative-parity vector, whose supported oscillator degrees are odd.

This is a repository Lean derivation consuming existing lattice, inversion, Virasoro and all-source twisted-law suppliers. The classical carrier convention remains FLM, PNAS 81 (1984), pp.3257--3258, equation (5); that announcement is not attributed a detailed proof of the finite derivative calculation. MixedJacobiFinite.mixed_jacobi proves the full signed mixed Jacobi law for this same coefficient on the actual fixed restricted dual under positive real Gram, unit determinant and rank twenty-four; MixedJacobi.actual_leech_vacuum_channel proves a nonzero I_3 channel on actual Golay Leech data. Full source BPZ/Riesz identification of that output with the original fixed source, skew exchange, three-twisted crossing, full fusion and anomaly structure, complete VOA/CFT, string theory and AdS/CFT remain separate obligations.

**Theorem 1.1 (All-vector standard-mode input translation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/MixedTranslation.normalizedCoefficient_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/MixedTranslation.normalizedCoefficient_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual rank-twenty-four lattice datum with unit determinant, every signed standard mode m and both actual negative-parity vectors u,v, the coefficient at translated u equals -m times the coefficient with mode m-1. The finite normalized-term recurrence and its exact boundary cancellation are live dependencies of the proof.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/MixedTranslation.normalizedCoefficient_translation`
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure](../GroundRightCurrentTransport/FirstSourceClosure.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalWard](../LatticeActualConformalWard.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal](../LatticeHalfFockCorrectedConformal.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/MixedIntertwiner](MixedIntertwiner.md)
