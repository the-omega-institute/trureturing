# Geometry of spectral compression

## Abstract

Geometry of spectral compression.

The real matrix A has rows (-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3), (-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4), and (-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2). All sixteen slots are retained.

**Definition 1.1 (Three boundary rows).**

$$A:Matrix\left(Fin\left(3\right), Fin\left(16\right), \mathbb{R}\right)=((-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3),(-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4),(-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A has three rows and sixteen ordered gap slots. Its minus-identity slack block retains every original row equation.

**Theorem 1.2 (Ordered boundary and middle positions).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.positions_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.positions_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N at least 67 and middle position j from 6 through N-10, the sixteen natural step positions 1,2,3,4,5,j,N-9 through N are strictly increasing. These positions and A are shared by the exact ray moments, the cofactor checker and the spectrum compression proof. The latter remains with the scalar endpoint and handles positive middle mass by barycentric weights and zero middle mass without division.

These statements concern real scalar spectra and finite cofactor certificates. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.positions_strict`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSpectralBound](../UniformSpectralBound.md)
