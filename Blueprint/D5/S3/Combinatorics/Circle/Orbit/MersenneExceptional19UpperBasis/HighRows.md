# Actual high-digit bridge for the upper-only exceptional19 presentation

## Abstract

Actual high-digit bridge for the upper-only exceptional19 presentation.

**Theorem 1.1 (actual high row differences).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows.actual_high_row_differences`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows.actual_high_row_differences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual high affine words have equal low parts and explicitly computed top three-bit quotients. Subtracting their readouts yields the six high equations. Unit-coefficient elimination and the one exceptional disjoint-union indicator establish the high normal form using only the selected masks.

**Theorem 1.2 (selected high normal form).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows.selected_high_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows.selected_high_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual high affine words have equal low parts and explicitly computed top three-bit quotients. Subtracting their readouts yields the six high equations. Unit-coefficient elimination and the one exceptional disjoint-union indicator establish the high normal form using only the selected masks.

The original presentation. For every natural r, including zero, d=18r+12 and E=2^(d-3)=B/8. SelectedAnnihilates is precisely the sum-zero condition on Family.selectedMask at each UpperIndex. The physical labels remain Fin(3d). affineRead reads the three existing words M+b, M and M-a through the sealed physical_read theorem. The private selection adapters recover only G, F and H UPPER rows already present in selectedMask.

Computing the actual seven top words. Integer floor inequalities from parameter_margins give the top-three-bit triples: R_(6E) has (7,6,5), R_(4E) has (5,4,3), R_(6E-b) has (6,4,3), R_(7E-b) has (7,5,4), R_(3E+a) has (5,3,3), R_a has (2,0,0), and R_(3E) has (4,3,2). The differences in each block are exact multiples of E, so the lower d-3 bits cancel by read_top_difference. These are derived physical digits, with no row-table hypothesis.

Unit high elimination. Writing the top three triples as (p,q,rh), (u,l,w), (x,y,z), the four actual differences read u+l-w+z; -p-q+rh+w-z; p+q+rh-u+l+w+x; and -p+q-rh+l-y. The selected T_(d-2) and the ONE disjoint-union indicator T_(d-3) union T_(d-1) supply u+l+w and p+q+rh+x+y+z. Integral linear combinations determine the high coordinates with t=l-q and theta=2q-l. The final unit pivot gives u=2p, without cancelling a scalar in A.

Why the union matters. The two exceptional triples are not separately zero rows. Their disjointness is used to evaluate their union as one indicator, exactly as selectedMask specifies. Thus the high calculation preserves the count 3d-1 and never enlarges the selected presentation. The new scripts reuse the existing generic sum_triple for the coordinate sums.

Source-only status. selected_high_normal_form is a candidate all-r arbitrary-group proof script. It is not compiled evidence. Boundary and EliminationFactors remain preserved predecessor work; their Schur factorization is not a prerequisite of this direct route.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows.actual_high_row_differences`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/HighRows.selected_high_normal_form`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows](../MersenneExceptional19PermutationStabilizer/CarryRows.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm](../MersenneExceptional19PermutationStabilizer/NormalForm.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/Physical](../MersenneExceptional19PermutationStabilizer/Physical.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19Stabilizer](../MersenneExceptional19Stabilizer.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/Readout](Readout.md)
