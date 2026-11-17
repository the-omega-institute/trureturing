# Integer correction incidence before torsion-sensitive descent

## Abstract

Integer correction incidence before torsion-sensitive descent.

**Theorem 1.1 (physical correction read).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.physical_correction_read`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.physical_correction_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations.

**Theorem 1.2 (affine correction integer zero).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.affine_correction_integer_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.affine_correction_integer_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations.

**Theorem 1.3 (corrected affine read).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.corrected_affine_read`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.corrected_affine_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations.

**Theorem 1.4 (selected corrected high).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.selected_corrected_high`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.selected_corrected_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six correction coefficients are read first as integer incidences. The existing affine digit identity proves their total is zero over integers. Distributivity then removes this correction from arbitrary-group affine readings and gives the selected corrected high equations.

The physical correction vector. The six nonzero entries of C are C_(1,d-3)=1, C_(1,d-2)=1, C_(2,d-2)=-1, C_(0,d-1)=-1, C_(1,d-1)=2 and C_(2,d-1)=-2. correctionBlock expresses C*theta by reusing the sealed first, middle and last normal-form functions with zero geometric generators. correctedBlock subtracts it from the original physical block labels. highTheta is exactly 2*g_(d-3)-g_(d-2).

Integer incidence, then arbitrary groups. The shared physical readouts and top_digits prove that reading correctionBlock on chi(L,M,U) equals correction(B,L,M,U)*theta. For a permitted affine row, the sealed affine_digits theorem already proves correction=0 in Z. affine_correction_integer_zero records this actual integer incidence, and corrected_affine_read consumes it to preserve the affine readout for arbitrary A. This reuses the stronger existing integer digit fact directly; it performs no cancellation of Q, 2 or any other scalar inside A.

Starting the descent. The six actual high equations from HighRows show that at levels d-3,d-2,d-1, the corrected blocks equal a single triple, twice that triple and four times that triple, with its sum zero. These are the initial invariants used by selected_corrected_ladders. They are derived from the selected presentation, rather than requested as assumptions in the final reconstruction.

The correction is computed from actual binary digits with integer coefficients. Its affine incidence vanishes before scalar multiplication in the target group, so no cancellation of a possibly nonunit scalar in an abelian group is used.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.affine_correction_integer_zero`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.corrected_affine_read`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.physical_correction_read`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Correction.selected_corrected_high`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows](HighRows.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19ZeroLattice/Readings](../MersenneExceptional19ZeroLattice/Readings.md)
