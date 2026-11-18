# Original return contact geometry

## Abstract

Whole-return compactness and stable source contacts in the original cone.

**Definition 1.1 (Entire return leakage).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.leakage`

*Formalization.* `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.leakage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

alpha_F(t) is the supremum of dist(x,F) over every x in D(t). Compactness makes it an attained maximum. The same auxiliary norm is used throughout. No selected subset of a return face is substituted.

**Definition 1.2 (Actual original maximum).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.baseMaximum`

*Formalization.* `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.baseMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M(b) is the supremum of b on the entire original K. For every nonzero original positive annihilator of an actual pure label, M(b)>0 and one fixed A>0 gives norm(b)<=A M(b). CommonSourceLiftObstruction.original_dual_bound supplies the original dual estimate for every signed functional, and its positive_base_norm identifies the whole-K state norm with M(b) for positive b. The original positive_annihilator_maximum gives strict positivity. M(b) has no imposed upper budget.

**Definition 1.3 (Additional common-sector condition).**

Lean statement: `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.sectorViolation`

*Formalization.* `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.sectorViolation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every one of the fixed dim(a)+1 source sectors has a nonzero original normal b, nonnegative on all of C and vanishing at the same actual t, with nonzero actual source slope, direction within theta of that sector, and norm(g_b)>H M(b) alpha_F(t). This is Q133.14 at one index. Its eventual sequence version is an extra antecedent and is not derived from exclusion balls, positive lifts or local pure-limit density. Normalized contrast is allowed to tend to zero.

The source uses the entire original finite real cone, normalized base, pure locus and effect interval. Its compactness argument includes mixed limit labels and repeated exclusion fibers. Sphere contacts include positive dimension one and the chart center. Positive barycentric reconstruction is stable both for a fixed source affine space and for one common affine space of bounded dimension. The whole_return_leakage, source_contact_simplex and uniform_return_sectors conclusions consume these ingredients through the original module. These are conditional mathematical results without a physical-realization claim.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.baseMaximum`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.leakage`
- Truth anchor: `D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.sectorViolation`
- Dependency: [D5/S3/Quantum/Foundation/CommonSourceLiftObstruction](../CommonSourceLiftObstruction.md)
- Dependency: [D5/S3/Quantum/Foundation/MixedExclusionGeometry](../MixedExclusionGeometry.md)
- Dependency: [D5/S3/Quantum/Foundation/SingleLabelNormalBody](../SingleLabelNormalBody.md)
- Dependency: [D5/S3/Quantum/Foundation/UniqueConfirmationDensity](../UniqueConfirmationDensity.md)
