# Cleared Kernel Action

## Abstract

Physical differences of supported native common-kernel expansions

For arbitrary D,a,b, an unrestricted oscillator polynomial p and a scalar power series h, E_h[k,l](p)=sum_(r>=0) coeff_r(h) J_ab[k+r,l-r](p). The actual rectangular kernel bounds prove finite support before any splitting or subtraction. The physical difference is D2 F[k,l]=F[k-2,l]-F[k,l-2]. Only the generic finite-support splitting supplier is reused; ordinary cover delta is not a twisted Jacobi certificate.

**Theorem 1.1 (One physical difference).**

$$\operatorname{PhysicalDifferenceExpansion}\left(D, a, b, h, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_expansion` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

D2 E_h[k,l]=E_((1-s^2)h)[k-2,l]. The proof splits off the first two finite-support terms and uses native PowerSeries coefficients of X^2 h, with every shifted sum proved finite.

**Theorem 1.2 (Native physical clearing).**

$$\operatorname{NativeClearedKernel}\left(D, a, b, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_expansion` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

At N=abs B(a,b), D2^N E_hg[k,l]=E_Pg[k-2N,l], using the exact two-branch scalar identity. This common-kernel statement alone does not prove actual charged tensor locality. Actual charged locality also uses the ordered products, polynomial reversal and actual ground signs. No twisted Jacobi, complete orbifold or string/AdS realization follows. Classical provenance, zero novelty claim.

**Theorem 1.3 (Exchange of the cleared native kernels).**

$$\operatorname{ClearedKernelExchange}\left(D, a, b, p, k, l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_exchange` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all D,a,b,p,k,l and N=abs B(a,b), D2^N E_ab[k,l] equals D2^N E_ba[l,k]. The fixed-degree reciprocal polynomial and the actual common-kernel branch exchange prove this equality by a finite coefficient reversal. No equality of the unregularized iota expansions is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_exchange`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_expansion`
- Dependency: [D5/S3/VertexAlgebra/BinomialKernelDelta](BinomialKernelDelta.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing](LatticeHalfFockBranchClearing.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockProductKernel](LatticeHalfFockProductKernel.md)
