# Signed source divided powers

## Abstract

Signed affine source and original finite L1 flow

For arbitrary original LatticeData D, charge a and finite oscillator polynomial p, affineP(p) is exactly SourceMobius.flowPolynomial applied after the weight-sign algebra map sigma(X(i,r))=(-1)^(r+1)*X(i,r). This is the signed source covariance, not unsigned substitution and not sigma after the flow. No determinant, positive norm or finite-dimensional full weight-space hypothesis is needed in this module.

The proof restores finite polynomial coordinates from the original variable_power and variable_power_charge calculations, reverses the finite binomial range, and compares algebra homomorphisms on generators. SourceMobius supplies the derivation, factorial recurrence and uniform nilpotence. weightSign_monomial and linear extension give sigma(p)=(-1)^R*p on each sourceWeight-homogeneous component. The classical coordinate-change background is FLM; no literature novelty or full VOA/string realization is claimed.

The faithful four-slot escape audit is unfinished under CLAUDE 3.9: https://github.com/the-omega-institute/trureturing/issues/21332. Reg mirrors reconstruct the full source laws, but complete enrolled-template realization, variation, sensitivity, observational dependence and current selector binding are not claimed.

**Theorem 1.1 (Exact signed divided powers).**

Lean statement: `D5/S3/VertexAlgebra/CorrectedInversion/SignedSource.affineP_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CorrectedInversion/SignedSource.affineP_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For p homogeneous of weight R and every natural k, affineP(D,a,p).coeff(k)=(-1)^R times (k!) inverse times sectorL1(D,a)^k(p). The sign is independent of k. This coefficient identity is consumed by actual_corrected_single_inversion.

**Theorem 1.2 (Native nilpotence gives the finite cutoff).**

Lean statement: `D5/S3/VertexAlgebra/CorrectedInversion/SignedSource.affineP_above_weight`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CorrectedInversion/SignedSource.affineP_above_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For k>R the same coefficient vanishes. The proof bounds weightedTotalDegree by R, uses the original finite flow expansion and sectorL1_degree_bound, and checks the finite polynomial coefficients. The zero polynomial and rank-zero cases are included. This is consumed when the corrected-field support sum is replaced by range(R+1).

## References

- Truth anchor: `D5/S3/VertexAlgebra/CorrectedInversion/SignedSource.affineP_above_weight`
- Truth anchor: `D5/S3/VertexAlgebra/CorrectedInversion/SignedSource.affineP_coeff`
- Dependency: [D5/S3/VertexAlgebra/CorrectedInversion/NormalReadout](NormalReadout.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/Coordinates](../SourceMobius/Coordinates.md)
