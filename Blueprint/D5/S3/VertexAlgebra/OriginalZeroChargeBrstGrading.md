# Native Integer Ghost Grading

## Abstract

The exceptional quotient is graded by the original integer ghost-number operator.

**Theorem 1.1 (Number operator on actual classes).**

$$\operatorname{cohomologyNumber}\left(\operatorname{class}\left(v\right)\right) = \operatorname{class}\left(\operatorname{cycleNumber}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.cohomologyNumber_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sector number operator is proved equal to the restriction of the original tensor J. Coordinates show it preserves cycles and descends on the exact quotient. The descended operator is not assumed to be a ghost-current zero mode.

**Theorem 1.2 (True integer eigenspaces).**

$$x \in \operatorname{gradedCohomology}\left(r\right) \iff \operatorname{cohomologyNumber}\left(x\right) = r\times x$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.mem_graded_iff_number` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A class belongs to degree r exactly when all its surviving coefficients outside degree r vanish. The proved native number correspondence identifies this support condition with the eigenvalue equation, rather than merely attaching integer labels to a basis.

**Theorem 1.3 (Every ghost degree).**

$$\operatorname{finrank}\left(Complex, \operatorname{gradedCohomology}\left(D, r\right)\right) = \operatorname{gradedDimension}\left(D, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.graded_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimensions are 1 in degree 0, rank(D) in degree 1, rank(D) in degree 2, 1 in degree 3, and zero in every other integer degree. The explicit survivor equivalence and homogeneous coordinate basis prove this table. At rank 26 it is 1, 26, 26, 1; this substitution contributes no new mathematical content.

The vacuum is assigned number zero. Every occupied creator in this energy fiber is a c creator, including the site-3 c0 mode, so its degree is its number of occupied sites. Conventions assigning a shifted number to the vacuum shift this table; they do not alter the actual source J or the native quotient.

**Theorem 1.4 (Homogeneous actual representatives).**

$$x \in \operatorname{gradedCohomology}\left(r\right) \Rightarrow \operatorname{class}\left(\operatorname{representative}\left(\operatorname{coordinates}\left(x\right)\right)\right) = x \land \operatorname{J}\left(\operatorname{representative}\left(\operatorname{coordinates}\left(x\right)\right)\right) = r\times \operatorname{representative}\left(\operatorname{coordinates}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.homogeneous_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every homogeneous quotient class, including every finite superposition, has the explicitly constructed actual cycle representative of that same integer J degree. Its class is exactly the original class, and the descended J agrees with applying the native J before taking the class. This is a proved representative construction, not a spectral assumption.

**Theorem 1.5 (Original Q and the shifted degree).**

$$\operatorname{homogeneousBoundary}\left(v, r\right) \Rightarrow \exists w, \operatorname{Q}\left(w\right) = v \land \operatorname{J}\left(w\right) = (r-1)\times w$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.original_boundary_homogeneous_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native J-Q commutator proves Q shifts integer degree by one. Every homogeneous actual boundary in degree r has an actual sector preimage in degree r-1. A nonzero boundary necessarily has degree 2 and is a multiple of the pure pair; its preimage is half that multiple of the c0 ground vector, of degree 1. The zero boundary has the zero preimage in every degree.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.cohomologyNumber_native`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.graded_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.homogeneous_representative`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.mem_graded_iff_number`
- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.original_boundary_homogeneous_preimage`
- Dependency: [D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology](OriginalZeroChargeBrstCohomology.md)
