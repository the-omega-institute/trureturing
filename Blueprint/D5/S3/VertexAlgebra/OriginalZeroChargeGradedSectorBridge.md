# Original Zero-Charge Quotient Identification

## Abstract

The native exceptional complex and the literal original zero-charge energy-sector quotients have the same representatives, boundaries and integral ghost grading.

The matter carrier is the unrestricted finite-support integral-charge polynomial Fock space tensored with the full exterior bc Fock space over the complex numbers. Both inverse-Gram equations are retained. Critical rank twenty-six is imposed where the literal original cohomology uses global nilpotence. No positive-signature assumption is imposed in the zero-charge branch.

**Theorem 1.1 (Equality Of Actual Energy Sectors).**

Lean statement: `D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge.sector_eq_original`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge.sector_eq_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Sigma-indexed native basis and the product-indexed original basis represent identical tensor monomials. The original charge projector acts diagonally in the native coordinates. Its fixed-point condition is exactly vanishing of every nonzero-charge coefficient, including arbitrary finite superpositions. The native zero-energy condition therefore identifies the whole original energy sector at charge zero and integer level one.

cohomologyEquiv identifies the full native quotient with OriginalBrstReassembly.Cohomology on the exact original sector and energyStable. Its cycle map and inverse preserve the underlying original state. boundary_correspondence identifies actual ranges of Q, not merely an ambient image. Both quotient maps are well-defined and their inverse laws are those of the constructed linear equivalence.

**Theorem 1.2 (Actual Integer Ghost Quotients).**

Lean statement: `D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge.gradedEquiv_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge.gradedEquiv_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

gradedEquiv identifies every native graded cohomology with the actual original ghostCohomology. An arbitrary homogeneous native class is represented using homogeneous_representative; an original homogeneous boundary has a predecessor-degree preimage using original_boundary_homogeneous_preimage. The resulting degree inclusion agrees with the full quotient identification, and cohomologyEquiv_number intertwines the actual original number operator J.

The dimensions are inherited from OriginalZeroChargeBrstGrading.graded_finrank and the existing survivor coordinates: degrees zero and three have dimension one, degrees one and two have dimension rank, and every other integer degree has dimension zero. At rank twenty-six the total dimension is fifty-four. The predecessor-degree preimage is a state in the exact original energy sector, with ghost degree one less than the boundary; it is not merely a preimage in an unrestricted ambient image. These dimensions and the native differential computation are reused mathematics, not separate new claims. The identification does not assert positivity of the exceptional physical form or any conclusion about Monster symmetry, denominator identities, string dynamics or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge.gradedEquiv_inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeGradedSectorBridge.sector_eq_original`
- Dependency: [D5/S3/VertexAlgebra/RelativePairing/AbsolutePhysicalNoGhost](RelativePairing/AbsolutePhysicalNoGhost.md)
