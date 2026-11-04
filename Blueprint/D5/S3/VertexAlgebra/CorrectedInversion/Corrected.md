# Original corrected-field inversion

## Abstract

Full original corrected-field finite L1 inversion

This result concerns the original correctedField, original Corr normalization and chosen bilinear actualForm on ActualTensor(D,hu), with only the original integer determinant-unit hypothesis hu. Charge norm N and coefficient index e remain arbitrary integers. The oscillator polynomial p is homogeneous of natural source weight R; no sign condition on N, form symmetry, finite full weight space, representability or assumed inversion is added.

Expand the actual left corrected coefficient using its original shift e+2c. Exact Corr coefficient bidegree gives weight R-c on each nonzero coefficient. The normal transpose therefore has exponent -(e+2c)-2N-4(R-c)+2t=-e-2N-4R+2(c+t). Corr_reflection_readout exchanges the two finite sums and the original shiftField rule reconstructs the right corrected field. The signed affine coefficient identity then substitutes (-1)^R*delta_a^j(p)/j!. Every finite sum is over actual polynomial supports before native nilpotence replaces the affine support by range(R+1).

The coordinate-change background is classical FLM. This is a source-faithful bridge between the existing native normal, Corr and SourceMobius kernels; it does not construct a complete VOA, fusion theory, Monster moonshine, string theory or AdS/CFT realization.

The faithful four-slot escape audit is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21332. Reg mirrors reconstruct the full source laws, but complete enrolled-template realization, variation, sensitivity, observational dependence and current selector binding are not claimed.

**Theorem 1.1 (Full homogeneous original-field inversion).**

Lean statement: `D5/S3/VertexAlgebra/CorrectedInversion/Corrected.actual_corrected_single_inversion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CorrectedInversion/Corrected.actual_corrected_single_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

B(Ycorr(single a p).coeff(e)x,y)=paritySign(N/2)*(-1)^R*sum(j=0..R) B(x,Ycorr(single a (delta_a^j(p)/j!)).coeff(-e-2N-4R+2j)y). Here delta_a is exactly SourceMobius.sectorL1, the original inverse-Gram Sugawara-1 sector derivation. Zero p, rank zero, repeated generators and arbitrary actual tensors are included. The proof consumes exact normal transpose, Corr bidegree and covariance, signed source-flow coefficients and native nilpotence.

**Theorem 1.2 (Consumed original monomial instance).**

Lean statement: `D5/S3/VertexAlgebra/CorrectedInversion/Corrected.actual_corrected_monomial_inversion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CorrectedInversion/Corrected.actual_corrected_monomial_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The homogeneous identity specializes to the existing monomial basis, with R equal to its sourceWeight. The resulting formula supplies dualReadout_monomial, which extends the corrected-field pairing identity linearly from monomials to arbitrary finitely supported source vectors.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CorrectedInversion/Corrected.actual_corrected_monomial_inversion`
- Truth anchor: `D5/S3/VertexAlgebra/CorrectedInversion/Corrected.actual_corrected_single_inversion`
- Dependency: [D5/S3/VertexAlgebra/CorrectedInversion/SignedSource](SignedSource.md)
