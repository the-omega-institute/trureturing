# Both Actual Charged Ordered Products

## Abstract

Both actual charged ordered products expand in the bounded common kernel.

Let D be any finite-rank ordinary lattice: its Gram matrix G is integral and symmetric with even diagonal. Rank zero is included. No positivity, nondegeneracy or unimodularity is assumed. Charges are Fin(rank(D)) to Z, oscillators are complex multivariate polynomials indexed by Fin(rank(D)) times N, and V is the finite-support charge direct sum of that polynomial algebra. Write B for the original integral bilinear form. Normalized coefficient q means the Laurent coefficient at -q-1. The vacuum is single(0,1), Y is the constructed actual state-field map, T is the charge-sensitive translation, and mu(a,q,b)=(Y(a))_q b.

Actual coefficient contraction, finite support on each intermediate vector, and induction on oscillator multiplication prove both operator orders. The common kernel has the actual output charge alpha+beta+delta. The reverse order is identified through kernel swap and the computed cocycle.

**Theorem 1.1 (First actual order in the common kernel).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_ordered_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

rawCoeff(alpha,k) rawCoeff(beta,l) single(delta,p) equals epsilon(alpha,beta) times the finite sum of (-1)^j choose(B(alpha,beta),j) K(k-B(alpha,beta)+j,l-j) on that input. Both intermediate-field truncation and kernel bounds are proved from the actual polynomials.

**Theorem 1.2 (Reverse actual order in the same kernel).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_reverse_ordered_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_reverse_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

rawCoeff(beta,l) rawCoeff(alpha,k) single(delta,p) equals epsilon(beta,alpha) times the finite sum with kernel indices (k-j,l-B(alpha,beta)+j). No desired expansion is a premise.

**Theorem 1.3 (Normalized modes preserve the raw product convention).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_ordered_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every integer m,n substitute k=-m-1 and l=-n-1 in the actual first ordered product. The operator order and both kernel index shifts are unchanged.

**Theorem 1.4 (Normalized reverse product).**

Lean statement: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_reverse_ordered_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_reverse_ordered_product` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The same substitution in the proved reverse coefficient product gives F_beta[n] F_alpha[m] on every actual single(delta,p). These are normalized mode identities from the whole ordered-product proof.

Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), DOI 10.1142/9789812702562_0001, supplies the lattice field, ordered-product, translation and conformal construction. Equation numbers refer to arXiv v1.

The carrier and formal-series interfaces use pinned Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d and Lean 4.33.0.

This is algebraic ungraded vertex-algebra mathematics. Finite graded pieces, positivity, PCT, Leech specialization, twisted extensions, the Monster, anomaly, fusion categories, string theory, AdS/CFT and physical completion are not proved here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_ordered_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_field_reverse_ordered_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_ordered_product`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeActualOrderedProducts.actual_reverse_ordered_product`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](LatticeActualProductKernel.md)
