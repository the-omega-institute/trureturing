# Supported Native Physical Rows

## Abstract

Finite native kernels for both actual physical residue branches.

**Theorem 1.1 (Each ordering has its own finite contraction expansion).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/Native.chargedPhysicalResidueRow_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/Native.chargedPhysicalResidueRow_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

On every pure actual tensor p tensor g, the complete row with matching sector signs (-1)^gamma=projectedSign epsilon and (-1)^delta=projectedSign eta is the difference of two finite sums of nativeOrderedKernel and nativeReversedKernel. The four reflected charged components are expanded before regrouping with the two matching sector equations. All integer indices and both lifts remain signed; the second ordering swaps charges and coefficient exponents.

For charges c,d and right exponent e, the contraction cutoff is (e+chargeNorm D d+sup{t(1):t in support(pairTranslation D c d p)}+1).toNat. Each occurrence uses its own e and pair-translated polynomial. The outer forward range comes from the order of B(p tensor g); the outer reverse range comes from the order of A(p tensor g). Common-kernel exchange and actual ground-action exchange put the reverse sum in the same orientation, with its exact paritySign(bilinear sigma tau) factor. The chargeScalar factors remain exact.

This finite kernel formula does not identify these sums with the binomial transform of collision coefficients. That change of variables is a further mathematical obligation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/Native.chargedPhysicalResidueRow_native`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/Locality](Locality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy](../LatticeHalfFockChargedMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality](../LatticeHalfFockPhysicalLocality.md)
