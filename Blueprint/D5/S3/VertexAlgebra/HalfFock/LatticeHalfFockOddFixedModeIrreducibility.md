# Native fixed-mode irreducibility

## Abstract

Irreducibility of the actual negative-parity half-Fock module under native fixed modes.

**Theorem 1.1 (Every stable submodule of the actual odd sector is bottom or top).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddFixedModeIrreducibility.fixedParitySlice_odd_irreducible`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddFixedModeIrreducibility.fixedParitySlice_odd_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Let D be a lattice datum of rank at least two with unit Gram determinant hu. Let S be any complex submodule of paritySpace D hu (-1). Assume that every integer mode of fixedParitySlice D hu (-1) at every source in FixedCarrier D maps S into S. Then S is bottom or top.

If S is nonzero, one-oscillator extraction gives a tensor X(a) tensor g in its ambient image with g nonzero. A creation operator after a partial derivative moves the oscillator to any index. For each charge, rank at least two gives a nonzero one-oscillator polarization in the kernel of the Gram pairing with that charge. The native fixed mode of the sum of the two opposite charge sources transports the ground vector along the charge lift. Reading a nonzero polarization coefficient moves the result back to X(a).

The ground vectors whose X(a) tensors lie in the image of S therefore form a charge-stable submodule. The shared groundSubrepresentation constructor gives the actual quotient action on it. Irreducibility of that representation and the nonzero ground seed give every ground vector. Induction on the odd occurrence list adds oscillator variables in pairs by two negative currents. Every ground coordinate of an odd vector is a finite sum of odd monomials, so these tensors fill S.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddFixedModeIrreducibility.fixedParitySlice_odd_irreducible`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/ActualFieldIrreducible](ActualFieldIrreducible.md)
- Dependency: [D5/S3/VertexAlgebra/HalfFock/LatticeHalfFockOddCyclicExtraction](LatticeHalfFockOddCyclicExtraction.md)
