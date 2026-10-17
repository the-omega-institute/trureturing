# Original rays and their moments

## Abstract

Original rays and their moments.

**Theorem 1.1 (Original rays and their moments).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RayMoments.ray_gram_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RayMoments.ray_gram_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original 187 identifiers retain their sixteen gap coordinates and their boundary, middle-envelope or bulk branch. Each ray uses the product of its gap vector, four integer moment coefficients u, v, c, C, and a Fin 4 branch label. Labels 0, 1, 2, 3 denote boundary, first middle envelope, second middle envelope, bulk. Validity is the conjunction of its five defining conditions. The integer position coefficients describe exactly 1,2,3,4,5,j,N-9 through N. MomentWitness records three linear mass coefficients and three quadratic Gram coefficients. A valid ray has nonnegative coefficients, positive mass throughout N at least 67 and j at least 6, exact moments and its branch certificate. These facts imply the Gram estimate throughout 6 at most j at most N-10. No distinctness of the ray labels is asserted.

These statements concern real scalar spectra and finite cofactor certificates. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RayMoments.ray_gram_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes](ScalarEnvelopes.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression](SpectrumCompression.md)
