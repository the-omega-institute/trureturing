# Charged Physical Locality

## Abstract

Charged half-Fock coefficients satisfy two-sheet physical locality on every actual tensor state.

For arbitrary integral symmetric even lattice data D, an integer determinant unit hu, charges left and right, integer exponents first and second, and every state in the dependent actual tensor representation, set N=(bilinear D left right).natAbs. The coefficient identity uses the physical shifts first-2*(N-offset) and second-2*offset and is independent of the exponent pair and target state.

The proof expands both ordered products through one bivariate polynomial kernel with rectangular lower support bounds and finite ordered-diagonal sums after fixing the polynomial. The bivariate kernel can have infinite support. The proof clears both half-contraction branches by (1-t^2)^N, uses the actual cocycle product and exchange including its normalization, and identifies the resulting finite signed binomial sum with the iterated doubled-shift difference. The pure tensor result is lifted to every ActualTensor vector by TensorProduct induction.

**Theorem 1.1 (Uniform two-sheet locality of charged coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D, hu, left, right, first, second and state in the original telescope, the displayed sum over Finset.range (N+1), with coefficient ((-1)^offset)*choose(N,offset), annihilates the difference of the two chargedCoefficient compositions. N is fixed before first, second and state. No positivity, rank, homogeneity, branch, eigenstate or locality hypothesis is added.

Bakalov–Kac, arXiv:math/0402315v1, section 4.1, equation (4.14), gives the untwisted ordered-product factor. The twisted root-of-unity branch product is in section 4.2, Lemma 4.2, equations (4.33)-(4.35). With cover order 2, sigma=-1, z=u^2 and w=v^2, equation (4.34) gives (u-v)^g*(u+v)^(-g), where g is the integral lattice pairing. These inspected formulas supply the classical mechanism; the exact arbitrary-D/hu coefficient theorem on the chosen quotient representation is repository-derived using canonical half-creation transport. The FLM reference is background; its full text was not inspected.

This result is algebraic and kernel-checked. Corrected normal-word locality, source-product compatibility, twisted Jacobi, analytic CFT completion, fusion and anomaly data, Moonshine, string theory and AdS/CFT remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel](LatticeHalfFockClearedKernel.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts](LatticeHalfFockGroundProducts.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts](LatticeHalfFockOrderedProducts.md)
