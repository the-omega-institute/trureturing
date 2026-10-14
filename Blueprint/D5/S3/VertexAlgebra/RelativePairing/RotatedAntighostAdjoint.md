# Rotated antighost transpose

## Abstract

The native energy rotation cancels the opposite-mode antighost transpose phase.

The ghost carrier is the full finite-support exterior bc Fock space over the complex numbers. The pairing is Gplus(left,right)=BPZ(left,rotation(right)), where rotation has the original integer conformal-energy phase. Hplus conjugates the left argument. Pi is the actual occupation-parity operator. No mode cutoff or replacement pairing is used.

**Theorem 1.1 (Bilinear opposite-mode transpose).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint.Gplus_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint.Gplus_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer mode, Gplus(b(mode) left,right)=Gplus(Pi left,b(-mode) right). The BPZ factor (-1)^mode and the rotation factor for the opposite mode coincide, giving this positive transpose sign.

**Theorem 1.2 (Conjugate-left opposite-mode transpose).**

Lean statement: `D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint.Hplus_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint.Hplus_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient conjugation commutes with b and Pi, hence Hplus(b(mode) left,right)=Hplus(Pi left,b(-mode) right). Tensoring this identity with the actual matter form supplies the antighost transpose needed for relative-kernel isotropy.

## References

- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint.Gplus_b`
- Truth anchor: `D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint.Hplus_b`
- Dependency: [D5/S3/VertexAlgebra/BcGhostRotatedForm](../BcGhostRotatedForm.md)
