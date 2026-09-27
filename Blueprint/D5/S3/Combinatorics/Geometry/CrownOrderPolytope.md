# Actual crown order polytopes

## Abstract

Finite exposed faces from active affine slacks.

The general active-slack argument is the implementation foundation for the classical geometric correspondence used in source Section 2 and Theorem 3.1; it is not claimed as new convex geometry.

**Theorem 1.1 (Active inequalities determine an exposed face).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytope.exposed_eq_active_of_finite_slacks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytope.exposed_eq_active_of_finite_slacks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For a finite family of real affine slacks on a finite-dimensional coordinate space, every exposed face containing an anchor is exactly the feasible points on which all slacks tight throughout that face vanish. The proof constructs a relative interior center by averaging finitely many witnesses and extends feasible segments through it. This is the geometric foundation for the crown face correspondence.

**Theorem 1.2 (Finitely many actual exposed faces).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytope.finite_crown_exposed_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytope.finite_crown_exposed_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every natural n, the exposed faces of the crown order polytope form a finite type. Faces are determined by subsets of its finite inequality family. The carrier is a set of real coordinate vectors with bounds zero and one and the alternating crown order inequalities; no combinatorial face-count formula is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytope.exposed_eq_active_of_finite_slacks`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytope.finite_crown_exposed_faces`
