# Actual Common Kernel and Intermediate Supports

## Abstract

Polynomial convolutions give finite intermediate-vector bounds for the actual common kernel.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

A one-variable polynomial convolution pairs a translated coefficient with creationCoeff(alpha,s+d). A two-variable convolution pairs each actual translated polynomial monomial with creationCoeff(alpha,u+e_0) creationCoeff(beta,v+e_1). Actual rawCoeff and commonKernel on single(delta,p) agree with these convolutions and their actual cocycle scalars.

**Theorem 1.1 (Both independent oscillator shifts of the kernel).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_creator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_creator` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Multiplication of p by X(i,n) gives its actual creator action on the common kernel, minus the alpha pairing times the shift u+n+1, minus the beta pairing times the shift v+n+1. Both translated variables are retained.

**Theorem 1.2 (Separate lower bounds on the actual kernel).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_lower_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_lower_bounds` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every alpha,beta,delta and polynomial p there exist integers a,b such that commonKernel(alpha,beta,u,v)(single(delta,p))=0 if u<a or v<b. The bounds come from the two coordinate maxima of the finite translatedPairPolynomial support and the actual charge pairings.

**Theorem 1.3 (Both ordered kernels have finite support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualProductKernel.ordered_kernel_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualProductKernel.ordered_kernel_finite` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all raw indices k,l the sequences K(k-B(alpha,beta)+j,l-j) and K(k-j,l-B(alpha,beta)+j), evaluated on the actual input, have finite support. The independent lower bounds control the decreasing coordinate in each branch.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_creator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualProductKernel.kernel_lower_bounds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualProductKernel.ordered_kernel_finite`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualGeneratorLocality](LatticeActualGeneratorLocality.md)
