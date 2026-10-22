# Native coefficient convolution supplier interfaces

## Abstract

Native coefficient convolution supplier interfaces

The generic coefficientConvolution and bivariateCoefficientConvolution definitions and proof bodies are the completed LatticeActualProductKernel supplier interfaces. They are installed in that original namespace without replacing the existing ordinary lattice convolution and pairConvolution declarations.

LatticeHalfFockOrderedProducts consumes the one-variable coefficient interface. LatticeHalfFockProductKernel consumes the bivariate coefficient interface to prove the actual half-creation kernel support. These are existing reusable supplier proofs, not additional mathematical novelty or separate bind-only formalization targets.

## References

- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](LatticeActualProductKernel.md)
